%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pvEG40j4hX

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:09 EST 2020

% Result     : Theorem 4.28s
% Output     : Refutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 107 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  577 ( 794 expanded)
%              Number of equality atoms :   51 (  73 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X6 ) )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_xboole_0 @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( ( k7_relat_1 @ X29 @ X28 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X6 ) )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t216_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t216_relat_1])).

thf('22',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k6_subset_1 @ X30 @ ( k7_relat_1 @ X30 @ X32 ) )
        = ( k7_relat_1 @ X30 @ ( k6_subset_1 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('36',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ X31 )
      | ( ( k4_xboole_0 @ X30 @ ( k7_relat_1 @ X30 @ X32 ) )
        = ( k7_relat_1 @ X30 @ ( k4_xboole_0 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) @ X27 )
        = ( k7_relat_1 @ X25 @ ( k3_xboole_0 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X25 @ X26 ) @ X27 )
        = ( k7_relat_1 @ X25 @ ( k1_setfam_1 @ ( k2_tarski @ X26 @ X27 ) ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X2 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = ( k7_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','43'])).

thf('45',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C_2 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('47',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C_2 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k7_relat_1 @ sk_C_2 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ( k7_relat_1 @ sk_C_2 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['11','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pvEG40j4hX
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:15:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.28/4.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.28/4.50  % Solved by: fo/fo7.sh
% 4.28/4.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.28/4.50  % done 7455 iterations in 4.044s
% 4.28/4.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.28/4.50  % SZS output start Refutation
% 4.28/4.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.28/4.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.28/4.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.28/4.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.28/4.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.28/4.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.28/4.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.28/4.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 4.28/4.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.28/4.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.28/4.50  thf(sk_B_type, type, sk_B: $i).
% 4.28/4.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.28/4.50  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 4.28/4.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 4.28/4.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.28/4.50  thf(sk_A_type, type, sk_A: $i).
% 4.28/4.50  thf(commutativity_k2_tarski, axiom,
% 4.28/4.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.28/4.50  thf('0', plain,
% 4.28/4.50      (![X19 : $i, X20 : $i]:
% 4.28/4.50         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 4.28/4.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.28/4.50  thf(t2_boole, axiom,
% 4.28/4.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 4.28/4.50  thf('1', plain,
% 4.28/4.50      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 4.28/4.50      inference('cnf', [status(esa)], [t2_boole])).
% 4.28/4.50  thf(t12_setfam_1, axiom,
% 4.28/4.50    (![A:$i,B:$i]:
% 4.28/4.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.28/4.50  thf('2', plain,
% 4.28/4.50      (![X23 : $i, X24 : $i]:
% 4.28/4.50         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 4.28/4.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.28/4.50  thf('3', plain,
% 4.28/4.50      (![X13 : $i]:
% 4.28/4.50         ((k1_setfam_1 @ (k2_tarski @ X13 @ k1_xboole_0)) = (k1_xboole_0))),
% 4.28/4.50      inference('demod', [status(thm)], ['1', '2'])).
% 4.28/4.50  thf('4', plain,
% 4.28/4.50      (![X0 : $i]:
% 4.28/4.50         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 4.28/4.50      inference('sup+', [status(thm)], ['0', '3'])).
% 4.28/4.50  thf(d7_xboole_0, axiom,
% 4.28/4.50    (![A:$i,B:$i]:
% 4.28/4.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 4.28/4.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 4.28/4.50  thf('5', plain,
% 4.28/4.50      (![X4 : $i, X6 : $i]:
% 4.28/4.50         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 4.28/4.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.28/4.50  thf('6', plain,
% 4.28/4.50      (![X23 : $i, X24 : $i]:
% 4.28/4.50         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 4.28/4.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.28/4.50  thf('7', plain,
% 4.28/4.50      (![X4 : $i, X6 : $i]:
% 4.28/4.50         ((r1_xboole_0 @ X4 @ X6)
% 4.28/4.50          | ((k1_setfam_1 @ (k2_tarski @ X4 @ X6)) != (k1_xboole_0)))),
% 4.28/4.50      inference('demod', [status(thm)], ['5', '6'])).
% 4.28/4.50  thf('8', plain,
% 4.28/4.50      (![X0 : $i]:
% 4.28/4.50         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 4.28/4.50      inference('sup-', [status(thm)], ['4', '7'])).
% 4.28/4.50  thf('9', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.28/4.50      inference('simplify', [status(thm)], ['8'])).
% 4.28/4.50  thf(t187_relat_1, axiom,
% 4.28/4.50    (![A:$i]:
% 4.28/4.50     ( ( v1_relat_1 @ A ) =>
% 4.28/4.50       ( ![B:$i]:
% 4.28/4.50         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 4.28/4.50           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 4.28/4.50  thf('10', plain,
% 4.28/4.50      (![X28 : $i, X29 : $i]:
% 4.28/4.50         (~ (r1_xboole_0 @ X28 @ (k1_relat_1 @ X29))
% 4.28/4.50          | ((k7_relat_1 @ X29 @ X28) = (k1_xboole_0))
% 4.28/4.50          | ~ (v1_relat_1 @ X29))),
% 4.28/4.50      inference('cnf', [status(esa)], [t187_relat_1])).
% 4.28/4.50  thf('11', plain,
% 4.28/4.50      (![X0 : $i]:
% 4.28/4.50         (~ (v1_relat_1 @ X0)
% 4.28/4.50          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 4.28/4.50      inference('sup-', [status(thm)], ['9', '10'])).
% 4.28/4.50  thf(t79_xboole_1, axiom,
% 4.28/4.50    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 4.28/4.50  thf('12', plain,
% 4.28/4.50      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 4.28/4.50      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.28/4.50  thf('13', plain,
% 4.28/4.50      (![X4 : $i, X5 : $i]:
% 4.28/4.50         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 4.28/4.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 4.28/4.50  thf('14', plain,
% 4.28/4.50      (![X23 : $i, X24 : $i]:
% 4.28/4.50         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 4.28/4.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.28/4.50  thf('15', plain,
% 4.28/4.50      (![X4 : $i, X5 : $i]:
% 4.28/4.50         (((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k1_xboole_0))
% 4.28/4.50          | ~ (r1_xboole_0 @ X4 @ X5))),
% 4.28/4.50      inference('demod', [status(thm)], ['13', '14'])).
% 4.28/4.50  thf('16', plain,
% 4.28/4.50      (![X0 : $i, X1 : $i]:
% 4.28/4.50         ((k1_setfam_1 @ (k2_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))
% 4.28/4.50           = (k1_xboole_0))),
% 4.28/4.50      inference('sup-', [status(thm)], ['12', '15'])).
% 4.28/4.50  thf('17', plain,
% 4.28/4.50      (![X19 : $i, X20 : $i]:
% 4.28/4.50         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 4.28/4.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.28/4.50  thf('18', plain,
% 4.28/4.50      (![X0 : $i, X1 : $i]:
% 4.28/4.50         ((k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 4.28/4.50           = (k1_xboole_0))),
% 4.28/4.50      inference('demod', [status(thm)], ['16', '17'])).
% 4.28/4.50  thf('19', plain,
% 4.28/4.50      (![X4 : $i, X6 : $i]:
% 4.28/4.50         ((r1_xboole_0 @ X4 @ X6)
% 4.28/4.50          | ((k1_setfam_1 @ (k2_tarski @ X4 @ X6)) != (k1_xboole_0)))),
% 4.28/4.50      inference('demod', [status(thm)], ['5', '6'])).
% 4.28/4.50  thf('20', plain,
% 4.28/4.50      (![X0 : $i, X1 : $i]:
% 4.28/4.50         (((k1_xboole_0) != (k1_xboole_0))
% 4.28/4.50          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.28/4.50      inference('sup-', [status(thm)], ['18', '19'])).
% 4.28/4.50  thf('21', plain,
% 4.28/4.50      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.28/4.50      inference('simplify', [status(thm)], ['20'])).
% 4.28/4.50  thf(t216_relat_1, conjecture,
% 4.28/4.50    (![A:$i,B:$i,C:$i]:
% 4.28/4.50     ( ( v1_relat_1 @ C ) =>
% 4.28/4.50       ( ( r1_tarski @ A @ B ) =>
% 4.28/4.50         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 4.28/4.50           ( k1_xboole_0 ) ) ) ))).
% 4.28/4.50  thf(zf_stmt_0, negated_conjecture,
% 4.28/4.50    (~( ![A:$i,B:$i,C:$i]:
% 4.28/4.50        ( ( v1_relat_1 @ C ) =>
% 4.28/4.50          ( ( r1_tarski @ A @ B ) =>
% 4.28/4.50            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 4.28/4.50              ( k1_xboole_0 ) ) ) ) )),
% 4.28/4.50    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 4.28/4.50  thf('22', plain, ((r1_tarski @ sk_A @ sk_B)),
% 4.28/4.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.50  thf(t63_xboole_1, axiom,
% 4.28/4.50    (![A:$i,B:$i,C:$i]:
% 4.28/4.50     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 4.28/4.50       ( r1_xboole_0 @ A @ C ) ))).
% 4.28/4.50  thf('23', plain,
% 4.28/4.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.28/4.50         (~ (r1_tarski @ X14 @ X15)
% 4.28/4.50          | ~ (r1_xboole_0 @ X15 @ X16)
% 4.28/4.50          | (r1_xboole_0 @ X14 @ X16))),
% 4.28/4.50      inference('cnf', [status(esa)], [t63_xboole_1])).
% 4.28/4.50  thf('24', plain,
% 4.28/4.50      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 4.28/4.50      inference('sup-', [status(thm)], ['22', '23'])).
% 4.28/4.50  thf('25', plain,
% 4.28/4.50      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 4.28/4.50      inference('sup-', [status(thm)], ['21', '24'])).
% 4.28/4.50  thf('26', plain,
% 4.28/4.50      (![X4 : $i, X5 : $i]:
% 4.28/4.50         (((k1_setfam_1 @ (k2_tarski @ X4 @ X5)) = (k1_xboole_0))
% 4.28/4.50          | ~ (r1_xboole_0 @ X4 @ X5))),
% 4.28/4.50      inference('demod', [status(thm)], ['13', '14'])).
% 4.28/4.50  thf('27', plain,
% 4.28/4.50      (![X0 : $i]:
% 4.28/4.50         ((k1_setfam_1 @ (k2_tarski @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))
% 4.28/4.50           = (k1_xboole_0))),
% 4.28/4.50      inference('sup-', [status(thm)], ['25', '26'])).
% 4.28/4.50  thf('28', plain,
% 4.28/4.50      (![X19 : $i, X20 : $i]:
% 4.28/4.50         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 4.28/4.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.28/4.50  thf(d3_tarski, axiom,
% 4.28/4.50    (![A:$i,B:$i]:
% 4.28/4.50     ( ( r1_tarski @ A @ B ) <=>
% 4.28/4.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.28/4.50  thf('29', plain,
% 4.28/4.50      (![X1 : $i, X3 : $i]:
% 4.28/4.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.28/4.50      inference('cnf', [status(esa)], [d3_tarski])).
% 4.28/4.50  thf('30', plain,
% 4.28/4.50      (![X1 : $i, X3 : $i]:
% 4.28/4.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.28/4.50      inference('cnf', [status(esa)], [d3_tarski])).
% 4.28/4.50  thf('31', plain,
% 4.28/4.50      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 4.28/4.50      inference('sup-', [status(thm)], ['29', '30'])).
% 4.28/4.50  thf('32', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 4.28/4.50      inference('simplify', [status(thm)], ['31'])).
% 4.28/4.50  thf(t211_relat_1, axiom,
% 4.28/4.50    (![A:$i,B:$i,C:$i]:
% 4.28/4.50     ( ( v1_relat_1 @ C ) =>
% 4.28/4.50       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 4.28/4.50         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 4.28/4.50           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 4.28/4.50  thf('33', plain,
% 4.28/4.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.28/4.50         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 4.28/4.50          | ((k6_subset_1 @ X30 @ (k7_relat_1 @ X30 @ X32))
% 4.28/4.50              = (k7_relat_1 @ X30 @ (k6_subset_1 @ X31 @ X32)))
% 4.28/4.50          | ~ (v1_relat_1 @ X30))),
% 4.28/4.50      inference('cnf', [status(esa)], [t211_relat_1])).
% 4.28/4.50  thf(redefinition_k6_subset_1, axiom,
% 4.28/4.50    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.28/4.50  thf('34', plain,
% 4.28/4.50      (![X21 : $i, X22 : $i]:
% 4.28/4.50         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 4.28/4.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.28/4.50  thf('35', plain,
% 4.28/4.50      (![X21 : $i, X22 : $i]:
% 4.28/4.50         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 4.28/4.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.28/4.50  thf('36', plain,
% 4.28/4.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.28/4.50         (~ (r1_tarski @ (k1_relat_1 @ X30) @ X31)
% 4.28/4.50          | ((k4_xboole_0 @ X30 @ (k7_relat_1 @ X30 @ X32))
% 4.28/4.50              = (k7_relat_1 @ X30 @ (k4_xboole_0 @ X31 @ X32)))
% 4.28/4.50          | ~ (v1_relat_1 @ X30))),
% 4.28/4.50      inference('demod', [status(thm)], ['33', '34', '35'])).
% 4.28/4.50  thf('37', plain,
% 4.28/4.50      (![X0 : $i, X1 : $i]:
% 4.28/4.50         (~ (v1_relat_1 @ X0)
% 4.28/4.50          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 4.28/4.50              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 4.28/4.50      inference('sup-', [status(thm)], ['32', '36'])).
% 4.28/4.50  thf(t100_relat_1, axiom,
% 4.28/4.50    (![A:$i,B:$i,C:$i]:
% 4.28/4.50     ( ( v1_relat_1 @ C ) =>
% 4.28/4.50       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 4.28/4.50         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 4.28/4.50  thf('38', plain,
% 4.28/4.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.28/4.50         (((k7_relat_1 @ (k7_relat_1 @ X25 @ X26) @ X27)
% 4.28/4.50            = (k7_relat_1 @ X25 @ (k3_xboole_0 @ X26 @ X27)))
% 4.28/4.50          | ~ (v1_relat_1 @ X25))),
% 4.28/4.50      inference('cnf', [status(esa)], [t100_relat_1])).
% 4.28/4.50  thf('39', plain,
% 4.28/4.50      (![X23 : $i, X24 : $i]:
% 4.28/4.50         ((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (k3_xboole_0 @ X23 @ X24))),
% 4.28/4.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.28/4.50  thf('40', plain,
% 4.28/4.50      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.28/4.50         (((k7_relat_1 @ (k7_relat_1 @ X25 @ X26) @ X27)
% 4.28/4.50            = (k7_relat_1 @ X25 @ (k1_setfam_1 @ (k2_tarski @ X26 @ X27))))
% 4.28/4.50          | ~ (v1_relat_1 @ X25))),
% 4.28/4.50      inference('demod', [status(thm)], ['38', '39'])).
% 4.28/4.50  thf('41', plain,
% 4.28/4.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.28/4.50         (((k7_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 4.28/4.50            = (k7_relat_1 @ X1 @ 
% 4.28/4.50               (k1_setfam_1 @ 
% 4.28/4.50                (k2_tarski @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2))))
% 4.28/4.50          | ~ (v1_relat_1 @ X1)
% 4.28/4.50          | ~ (v1_relat_1 @ X1))),
% 4.28/4.50      inference('sup+', [status(thm)], ['37', '40'])).
% 4.28/4.50  thf('42', plain,
% 4.28/4.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.28/4.50         (~ (v1_relat_1 @ X1)
% 4.28/4.50          | ((k7_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 4.28/4.50              = (k7_relat_1 @ X1 @ 
% 4.28/4.50                 (k1_setfam_1 @ 
% 4.28/4.50                  (k2_tarski @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X2)))))),
% 4.28/4.50      inference('simplify', [status(thm)], ['41'])).
% 4.28/4.50  thf('43', plain,
% 4.28/4.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.28/4.50         (((k7_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 4.28/4.50            = (k7_relat_1 @ X1 @ 
% 4.28/4.50               (k1_setfam_1 @ 
% 4.28/4.50                (k2_tarski @ X2 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0)))))
% 4.28/4.50          | ~ (v1_relat_1 @ X1))),
% 4.28/4.50      inference('sup+', [status(thm)], ['28', '42'])).
% 4.28/4.50  thf('44', plain,
% 4.28/4.50      (![X0 : $i]:
% 4.28/4.50         (((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 4.28/4.50            = (k7_relat_1 @ X0 @ k1_xboole_0))
% 4.28/4.50          | ~ (v1_relat_1 @ X0))),
% 4.28/4.50      inference('sup+', [status(thm)], ['27', '43'])).
% 4.28/4.50  thf('45', plain,
% 4.28/4.50      (((k7_relat_1 @ (k6_subset_1 @ sk_C_2 @ (k7_relat_1 @ sk_C_2 @ sk_B)) @ 
% 4.28/4.50         sk_A) != (k1_xboole_0))),
% 4.28/4.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.50  thf('46', plain,
% 4.28/4.50      (![X21 : $i, X22 : $i]:
% 4.28/4.50         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 4.28/4.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 4.28/4.50  thf('47', plain,
% 4.28/4.50      (((k7_relat_1 @ (k4_xboole_0 @ sk_C_2 @ (k7_relat_1 @ sk_C_2 @ sk_B)) @ 
% 4.28/4.50         sk_A) != (k1_xboole_0))),
% 4.28/4.50      inference('demod', [status(thm)], ['45', '46'])).
% 4.28/4.50  thf('48', plain,
% 4.28/4.50      ((((k7_relat_1 @ sk_C_2 @ k1_xboole_0) != (k1_xboole_0))
% 4.28/4.50        | ~ (v1_relat_1 @ sk_C_2))),
% 4.28/4.50      inference('sup-', [status(thm)], ['44', '47'])).
% 4.28/4.50  thf('49', plain, ((v1_relat_1 @ sk_C_2)),
% 4.28/4.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.50  thf('50', plain, (((k7_relat_1 @ sk_C_2 @ k1_xboole_0) != (k1_xboole_0))),
% 4.28/4.50      inference('demod', [status(thm)], ['48', '49'])).
% 4.28/4.50  thf('51', plain,
% 4.28/4.50      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C_2))),
% 4.28/4.50      inference('sup-', [status(thm)], ['11', '50'])).
% 4.28/4.50  thf('52', plain, ((v1_relat_1 @ sk_C_2)),
% 4.28/4.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.50  thf('53', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 4.28/4.50      inference('demod', [status(thm)], ['51', '52'])).
% 4.28/4.50  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 4.28/4.50  
% 4.28/4.50  % SZS output end Refutation
% 4.28/4.50  
% 4.28/4.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
