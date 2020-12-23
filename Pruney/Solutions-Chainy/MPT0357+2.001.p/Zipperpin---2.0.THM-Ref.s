%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wt65GFe7Ka

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:20 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 124 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  596 ( 943 expanded)
%              Number of equality atoms :   56 (  68 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t36_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
             => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('8',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( r1_tarski @ X25 @ X23 )
      | ( X24
       != ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('10',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['8','10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','19'])).

thf('21',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','28'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('34',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('41',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('45',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('47',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['34','53'])).

thf('55',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['31','54'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('60',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('63',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['0','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wt65GFe7Ka
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 1.33/1.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.33/1.50  % Solved by: fo/fo7.sh
% 1.33/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.33/1.50  % done 3413 iterations in 1.055s
% 1.33/1.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.33/1.50  % SZS output start Refutation
% 1.33/1.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.33/1.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.33/1.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.33/1.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.33/1.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.33/1.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.33/1.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.33/1.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.33/1.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.33/1.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.33/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.33/1.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.33/1.50  thf(sk_B_type, type, sk_B: $i).
% 1.33/1.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.33/1.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.33/1.50  thf(t36_subset_1, conjecture,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.33/1.50       ( ![C:$i]:
% 1.33/1.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.33/1.50           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 1.33/1.50             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 1.33/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.33/1.50    (~( ![A:$i,B:$i]:
% 1.33/1.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.33/1.50          ( ![C:$i]:
% 1.33/1.50            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.33/1.50              ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 1.33/1.50                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ) )),
% 1.33/1.50    inference('cnf.neg', [status(esa)], [t36_subset_1])).
% 1.33/1.50  thf('0', plain, (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B)),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf(d5_subset_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.33/1.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.33/1.50  thf('2', plain,
% 1.33/1.50      (![X32 : $i, X33 : $i]:
% 1.33/1.50         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 1.33/1.50          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 1.33/1.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.33/1.50  thf('3', plain,
% 1.33/1.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.33/1.50      inference('sup-', [status(thm)], ['1', '2'])).
% 1.33/1.50  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf(d2_subset_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( ( v1_xboole_0 @ A ) =>
% 1.33/1.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.33/1.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.33/1.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.33/1.50  thf('5', plain,
% 1.33/1.50      (![X29 : $i, X30 : $i]:
% 1.33/1.50         (~ (m1_subset_1 @ X29 @ X30)
% 1.33/1.50          | (r2_hidden @ X29 @ X30)
% 1.33/1.50          | (v1_xboole_0 @ X30))),
% 1.33/1.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.33/1.50  thf('6', plain,
% 1.33/1.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.33/1.50        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.33/1.50      inference('sup-', [status(thm)], ['4', '5'])).
% 1.33/1.50  thf(fc1_subset_1, axiom,
% 1.33/1.50    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.33/1.50  thf('7', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 1.33/1.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.33/1.50  thf('8', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.33/1.50      inference('clc', [status(thm)], ['6', '7'])).
% 1.33/1.50  thf(d1_zfmisc_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.33/1.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.33/1.50  thf('9', plain,
% 1.33/1.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.33/1.50         (~ (r2_hidden @ X25 @ X24)
% 1.33/1.50          | (r1_tarski @ X25 @ X23)
% 1.33/1.50          | ((X24) != (k1_zfmisc_1 @ X23)))),
% 1.33/1.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.33/1.50  thf('10', plain,
% 1.33/1.50      (![X23 : $i, X25 : $i]:
% 1.33/1.50         ((r1_tarski @ X25 @ X23) | ~ (r2_hidden @ X25 @ (k1_zfmisc_1 @ X23)))),
% 1.33/1.50      inference('simplify', [status(thm)], ['9'])).
% 1.33/1.50  thf('11', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 1.33/1.50      inference('sup-', [status(thm)], ['8', '10'])).
% 1.33/1.50  thf(l32_xboole_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.33/1.50  thf('12', plain,
% 1.33/1.50      (![X2 : $i, X4 : $i]:
% 1.33/1.50         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 1.33/1.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.33/1.50  thf('13', plain, (((k4_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['11', '12'])).
% 1.33/1.50  thf(t48_xboole_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.33/1.50  thf('14', plain,
% 1.33/1.50      (![X13 : $i, X14 : $i]:
% 1.33/1.50         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.33/1.50           = (k3_xboole_0 @ X13 @ X14))),
% 1.33/1.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.33/1.50  thf('15', plain,
% 1.33/1.50      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.33/1.50      inference('sup+', [status(thm)], ['13', '14'])).
% 1.33/1.50  thf(t3_boole, axiom,
% 1.33/1.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.33/1.50  thf('16', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.33/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.33/1.50  thf('17', plain, (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.33/1.50      inference('demod', [status(thm)], ['15', '16'])).
% 1.33/1.50  thf(t49_xboole_1, axiom,
% 1.33/1.50    (![A:$i,B:$i,C:$i]:
% 1.33/1.50     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.33/1.50       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.33/1.50  thf('18', plain,
% 1.33/1.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.33/1.50         ((k3_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X17))
% 1.33/1.50           = (k4_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X17))),
% 1.33/1.50      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.33/1.50  thf('19', plain,
% 1.33/1.50      (![X0 : $i]:
% 1.33/1.50         ((k3_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ X0))
% 1.33/1.50           = (k4_xboole_0 @ sk_C_1 @ X0))),
% 1.33/1.50      inference('sup+', [status(thm)], ['17', '18'])).
% 1.33/1.50  thf('20', plain,
% 1.33/1.50      (((k3_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))
% 1.33/1.50         = (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 1.33/1.50      inference('sup+', [status(thm)], ['3', '19'])).
% 1.33/1.50  thf('21', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1)),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf('22', plain,
% 1.33/1.50      (![X2 : $i, X4 : $i]:
% 1.33/1.50         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 1.33/1.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.33/1.50  thf('23', plain,
% 1.33/1.50      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['21', '22'])).
% 1.33/1.50  thf('24', plain,
% 1.33/1.50      (![X13 : $i, X14 : $i]:
% 1.33/1.50         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.33/1.50           = (k3_xboole_0 @ X13 @ X14))),
% 1.33/1.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.33/1.50  thf('25', plain,
% 1.33/1.50      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.33/1.50         = (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 1.33/1.50      inference('sup+', [status(thm)], ['23', '24'])).
% 1.33/1.50  thf('26', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.33/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.33/1.50  thf(commutativity_k3_xboole_0, axiom,
% 1.33/1.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.33/1.50  thf('27', plain,
% 1.33/1.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.33/1.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.33/1.50  thf('28', plain,
% 1.33/1.50      (((k3_subset_1 @ sk_A @ sk_B)
% 1.33/1.50         = (k3_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 1.33/1.50      inference('demod', [status(thm)], ['25', '26', '27'])).
% 1.33/1.50  thf('29', plain,
% 1.33/1.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_C_1 @ sk_B))),
% 1.33/1.50      inference('sup+', [status(thm)], ['20', '28'])).
% 1.33/1.50  thf(t39_xboole_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.33/1.50  thf('30', plain,
% 1.33/1.50      (![X8 : $i, X9 : $i]:
% 1.33/1.50         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.33/1.50           = (k2_xboole_0 @ X8 @ X9))),
% 1.33/1.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.33/1.50  thf('31', plain,
% 1.33/1.50      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.33/1.50         = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 1.33/1.50      inference('sup+', [status(thm)], ['29', '30'])).
% 1.33/1.50  thf('32', plain,
% 1.33/1.50      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.33/1.50      inference('sup-', [status(thm)], ['1', '2'])).
% 1.33/1.50  thf('33', plain,
% 1.33/1.50      (![X8 : $i, X9 : $i]:
% 1.33/1.50         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.33/1.50           = (k2_xboole_0 @ X8 @ X9))),
% 1.33/1.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.33/1.50  thf('34', plain,
% 1.33/1.50      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.33/1.50         = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.33/1.50      inference('sup+', [status(thm)], ['32', '33'])).
% 1.33/1.50  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf('36', plain,
% 1.33/1.50      (![X29 : $i, X30 : $i]:
% 1.33/1.50         (~ (m1_subset_1 @ X29 @ X30)
% 1.33/1.50          | (r2_hidden @ X29 @ X30)
% 1.33/1.50          | (v1_xboole_0 @ X30))),
% 1.33/1.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.33/1.50  thf('37', plain,
% 1.33/1.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.33/1.50        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.33/1.50      inference('sup-', [status(thm)], ['35', '36'])).
% 1.33/1.50  thf('38', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 1.33/1.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.33/1.50  thf('39', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.33/1.50      inference('clc', [status(thm)], ['37', '38'])).
% 1.33/1.50  thf('40', plain,
% 1.33/1.50      (![X23 : $i, X25 : $i]:
% 1.33/1.50         ((r1_tarski @ X25 @ X23) | ~ (r2_hidden @ X25 @ (k1_zfmisc_1 @ X23)))),
% 1.33/1.50      inference('simplify', [status(thm)], ['9'])).
% 1.33/1.50  thf('41', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.33/1.50      inference('sup-', [status(thm)], ['39', '40'])).
% 1.33/1.50  thf('42', plain,
% 1.33/1.50      (![X2 : $i, X4 : $i]:
% 1.33/1.50         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 1.33/1.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.33/1.50  thf('43', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.33/1.50      inference('sup-', [status(thm)], ['41', '42'])).
% 1.33/1.50  thf('44', plain,
% 1.33/1.50      (![X8 : $i, X9 : $i]:
% 1.33/1.50         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 1.33/1.50           = (k2_xboole_0 @ X8 @ X9))),
% 1.33/1.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.33/1.50  thf('45', plain,
% 1.33/1.50      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B))),
% 1.33/1.50      inference('sup+', [status(thm)], ['43', '44'])).
% 1.33/1.50  thf(t1_boole, axiom,
% 1.33/1.50    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.33/1.50  thf('46', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 1.33/1.50      inference('cnf', [status(esa)], [t1_boole])).
% 1.33/1.50  thf('47', plain, (((sk_A) = (k2_xboole_0 @ sk_A @ sk_B))),
% 1.33/1.50      inference('demod', [status(thm)], ['45', '46'])).
% 1.33/1.50  thf(commutativity_k2_tarski, axiom,
% 1.33/1.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.33/1.50  thf('48', plain,
% 1.33/1.50      (![X18 : $i, X19 : $i]:
% 1.33/1.50         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 1.33/1.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.33/1.50  thf(l51_zfmisc_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.33/1.50  thf('49', plain,
% 1.33/1.50      (![X27 : $i, X28 : $i]:
% 1.33/1.50         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 1.33/1.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.33/1.50  thf('50', plain,
% 1.33/1.50      (![X0 : $i, X1 : $i]:
% 1.33/1.50         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.33/1.50      inference('sup+', [status(thm)], ['48', '49'])).
% 1.33/1.50  thf('51', plain,
% 1.33/1.50      (![X27 : $i, X28 : $i]:
% 1.33/1.50         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 1.33/1.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.33/1.50  thf('52', plain,
% 1.33/1.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.33/1.50      inference('sup+', [status(thm)], ['50', '51'])).
% 1.33/1.50  thf('53', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_A))),
% 1.33/1.50      inference('demod', [status(thm)], ['47', '52'])).
% 1.33/1.50  thf('54', plain,
% 1.33/1.50      (((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_A))),
% 1.33/1.50      inference('demod', [status(thm)], ['34', '53'])).
% 1.33/1.50  thf('55', plain, (((k2_xboole_0 @ sk_B @ sk_C_1) = (sk_A))),
% 1.33/1.50      inference('sup+', [status(thm)], ['31', '54'])).
% 1.33/1.50  thf(t40_xboole_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]:
% 1.33/1.50     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.33/1.50  thf('56', plain,
% 1.33/1.50      (![X11 : $i, X12 : $i]:
% 1.33/1.50         ((k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ X12)
% 1.33/1.50           = (k4_xboole_0 @ X11 @ X12))),
% 1.33/1.50      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.33/1.50  thf('57', plain,
% 1.33/1.50      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 1.33/1.50      inference('sup+', [status(thm)], ['55', '56'])).
% 1.33/1.50  thf('58', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.33/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.33/1.50  thf('59', plain,
% 1.33/1.50      (![X32 : $i, X33 : $i]:
% 1.33/1.50         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 1.33/1.50          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 1.33/1.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.33/1.50  thf('60', plain,
% 1.33/1.50      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 1.33/1.50      inference('sup-', [status(thm)], ['58', '59'])).
% 1.33/1.50  thf('61', plain,
% 1.33/1.50      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_B @ sk_C_1))),
% 1.33/1.50      inference('sup+', [status(thm)], ['57', '60'])).
% 1.33/1.50  thf(t36_xboole_1, axiom,
% 1.33/1.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.33/1.50  thf('62', plain,
% 1.33/1.50      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.33/1.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.33/1.50  thf('63', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B)),
% 1.33/1.50      inference('sup+', [status(thm)], ['61', '62'])).
% 1.33/1.50  thf('64', plain, ($false), inference('demod', [status(thm)], ['0', '63'])).
% 1.33/1.50  
% 1.33/1.50  % SZS output end Refutation
% 1.33/1.50  
% 1.33/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
