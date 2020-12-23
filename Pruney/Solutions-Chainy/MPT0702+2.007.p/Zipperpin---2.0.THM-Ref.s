%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YXPixgWwv0

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:43 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 188 expanded)
%              Number of leaves         :   37 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  865 (1457 expanded)
%              Number of equality atoms :   90 ( 139 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_3 @ sk_A ) @ ( k9_relat_1 @ sk_C_3 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k6_subset_1 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_C_3 @ sk_A ) @ ( k9_relat_1 @ sk_C_3 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X119: $i,X120: $i,X121: $i] :
      ( ~ ( v2_funct_1 @ X119 )
      | ( ( k9_relat_1 @ X119 @ ( k6_subset_1 @ X120 @ X121 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X119 @ X120 ) @ ( k9_relat_1 @ X119 @ X121 ) ) )
      | ~ ( v1_funct_1 @ X119 )
      | ~ ( v1_relat_1 @ X119 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('7',plain,
    ( ( ( k9_relat_1 @ sk_C_3 @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v2_funct_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k9_relat_1 @ sk_C_3 @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X115: $i,X116: $i] :
      ( ( ( k9_relat_1 @ X115 @ X116 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X115 ) @ X116 )
      | ~ ( v1_relat_1 @ X115 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_3 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_3 ) @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_3 ) @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_C_3 ) @ ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    r1_xboole_0 @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X40 @ X41 ) @ X41 )
        = X40 )
      | ~ ( r1_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('24',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('26',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k6_subset_1 @ X27 @ X28 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k6_subset_1 @ X40 @ X41 )
        = X40 )
      | ~ ( r1_xboole_0 @ X40 @ X41 ) ) ),
    inference(demod,[status(thm)],['23','24','28'])).

thf('30',plain,
    ( ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_C_3 ) )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('31',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t111_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X16 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('33',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('34',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X16 @ X18 ) @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k3_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('40',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('41',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k3_xboole_0 @ X31 @ ( k6_subset_1 @ X32 @ X33 ) )
      = ( k6_subset_1 @ ( k3_xboole_0 @ X31 @ X32 ) @ X33 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','42'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X21: $i] :
      ( ( k2_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k6_subset_1 @ X27 @ X28 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('54',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ X12 @ X13 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('58',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ X12 @ X13 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('63',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('65',plain,(
    ! [X26: $i] :
      ( ( k6_subset_1 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('70',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','72'])).

thf('74',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_3 ) @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['30','73'])).

thf('75',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k3_xboole_0 @ X31 @ ( k6_subset_1 @ X32 @ X33 ) )
      = ( k6_subset_1 @ ( k3_xboole_0 @ X31 @ X32 ) @ X33 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('76',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('77',plain,(
    ! [X109: $i,X110: $i] :
      ( ( k6_subset_1 @ X109 @ X110 )
      = ( k4_xboole_0 @ X109 @ X110 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('78',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k6_subset_1 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_3 ) @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('82',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('83',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_C_3 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','84'])).

thf('86',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YXPixgWwv0
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:38:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.65/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.92  % Solved by: fo/fo7.sh
% 0.65/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.92  % done 1570 iterations in 0.478s
% 0.65/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.92  % SZS output start Refutation
% 0.65/0.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.65/0.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.65/0.92  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.65/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.65/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.65/0.92  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.65/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.92  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.65/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.65/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.65/0.92  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.65/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.65/0.92  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.65/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.65/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.92  thf(t157_funct_1, conjecture,
% 0.65/0.92    (![A:$i,B:$i,C:$i]:
% 0.65/0.92     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.65/0.92       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.65/0.92           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.65/0.92         ( r1_tarski @ A @ B ) ) ))).
% 0.65/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.92    (~( ![A:$i,B:$i,C:$i]:
% 0.65/0.92        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.65/0.92          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.65/0.92              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.65/0.92            ( r1_tarski @ A @ B ) ) ) )),
% 0.65/0.92    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.65/0.92  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.65/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.92  thf('1', plain,
% 0.65/0.92      ((r1_tarski @ (k9_relat_1 @ sk_C_3 @ sk_A) @ (k9_relat_1 @ sk_C_3 @ sk_B))),
% 0.65/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.92  thf(l32_xboole_1, axiom,
% 0.65/0.92    (![A:$i,B:$i]:
% 0.65/0.92     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.65/0.92  thf('2', plain,
% 0.65/0.92      (![X9 : $i, X11 : $i]:
% 0.65/0.92         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.65/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.65/0.92  thf(redefinition_k6_subset_1, axiom,
% 0.65/0.92    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.65/0.92  thf('3', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('4', plain,
% 0.65/0.92      (![X9 : $i, X11 : $i]:
% 0.65/0.92         (((k6_subset_1 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 0.65/0.92      inference('demod', [status(thm)], ['2', '3'])).
% 0.65/0.92  thf('5', plain,
% 0.65/0.92      (((k6_subset_1 @ (k9_relat_1 @ sk_C_3 @ sk_A) @ 
% 0.65/0.92         (k9_relat_1 @ sk_C_3 @ sk_B)) = (k1_xboole_0))),
% 0.65/0.92      inference('sup-', [status(thm)], ['1', '4'])).
% 0.65/0.92  thf(t123_funct_1, axiom,
% 0.65/0.92    (![A:$i,B:$i,C:$i]:
% 0.65/0.92     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.65/0.92       ( ( v2_funct_1 @ C ) =>
% 0.65/0.92         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.65/0.92           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.65/0.92  thf('6', plain,
% 0.65/0.92      (![X119 : $i, X120 : $i, X121 : $i]:
% 0.65/0.92         (~ (v2_funct_1 @ X119)
% 0.65/0.92          | ((k9_relat_1 @ X119 @ (k6_subset_1 @ X120 @ X121))
% 0.65/0.92              = (k6_subset_1 @ (k9_relat_1 @ X119 @ X120) @ 
% 0.65/0.92                 (k9_relat_1 @ X119 @ X121)))
% 0.65/0.92          | ~ (v1_funct_1 @ X119)
% 0.65/0.92          | ~ (v1_relat_1 @ X119))),
% 0.65/0.92      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.65/0.92  thf('7', plain,
% 0.65/0.92      ((((k9_relat_1 @ sk_C_3 @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.65/0.92        | ~ (v1_relat_1 @ sk_C_3)
% 0.65/0.92        | ~ (v1_funct_1 @ sk_C_3)
% 0.65/0.92        | ~ (v2_funct_1 @ sk_C_3))),
% 0.65/0.92      inference('sup+', [status(thm)], ['5', '6'])).
% 0.65/0.92  thf('8', plain, ((v1_relat_1 @ sk_C_3)),
% 0.65/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.92  thf('9', plain, ((v1_funct_1 @ sk_C_3)),
% 0.65/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.92  thf('10', plain, ((v2_funct_1 @ sk_C_3)),
% 0.65/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.92  thf('11', plain,
% 0.65/0.92      (((k9_relat_1 @ sk_C_3 @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.65/0.92      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.65/0.92  thf(t151_relat_1, axiom,
% 0.65/0.92    (![A:$i,B:$i]:
% 0.65/0.92     ( ( v1_relat_1 @ B ) =>
% 0.65/0.92       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.65/0.92         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.65/0.92  thf('12', plain,
% 0.65/0.92      (![X115 : $i, X116 : $i]:
% 0.65/0.92         (((k9_relat_1 @ X115 @ X116) != (k1_xboole_0))
% 0.65/0.92          | (r1_xboole_0 @ (k1_relat_1 @ X115) @ X116)
% 0.65/0.92          | ~ (v1_relat_1 @ X115))),
% 0.65/0.92      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.65/0.92  thf('13', plain,
% 0.65/0.92      ((((k1_xboole_0) != (k1_xboole_0))
% 0.65/0.92        | ~ (v1_relat_1 @ sk_C_3)
% 0.65/0.92        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_3) @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.65/0.92      inference('sup-', [status(thm)], ['11', '12'])).
% 0.65/0.92  thf('14', plain, ((v1_relat_1 @ sk_C_3)),
% 0.65/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.92  thf('15', plain,
% 0.65/0.92      ((((k1_xboole_0) != (k1_xboole_0))
% 0.65/0.92        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_3) @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.65/0.92      inference('demod', [status(thm)], ['13', '14'])).
% 0.65/0.92  thf('16', plain,
% 0.65/0.92      ((r1_xboole_0 @ (k1_relat_1 @ sk_C_3) @ (k6_subset_1 @ sk_A @ sk_B))),
% 0.65/0.92      inference('simplify', [status(thm)], ['15'])).
% 0.65/0.92  thf(t4_xboole_0, axiom,
% 0.65/0.92    (![A:$i,B:$i]:
% 0.65/0.92     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.65/0.92            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.65/0.92       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.65/0.92            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.65/0.92  thf('17', plain,
% 0.65/0.92      (![X5 : $i, X6 : $i]:
% 0.65/0.92         ((r1_xboole_0 @ X5 @ X6)
% 0.65/0.92          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.65/0.92      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.65/0.92  thf(commutativity_k3_xboole_0, axiom,
% 0.65/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.65/0.92  thf('18', plain,
% 0.65/0.92      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.65/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.92  thf('19', plain,
% 0.65/0.92      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.65/0.92         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.65/0.92          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.65/0.92      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.65/0.92  thf('20', plain,
% 0.65/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.92         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.65/0.92          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.65/0.92      inference('sup-', [status(thm)], ['18', '19'])).
% 0.65/0.92  thf('21', plain,
% 0.65/0.92      (![X0 : $i, X1 : $i]:
% 0.65/0.92         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.65/0.92      inference('sup-', [status(thm)], ['17', '20'])).
% 0.65/0.92  thf('22', plain,
% 0.65/0.92      ((r1_xboole_0 @ (k6_subset_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_C_3))),
% 0.65/0.92      inference('sup-', [status(thm)], ['16', '21'])).
% 0.65/0.92  thf(t88_xboole_1, axiom,
% 0.65/0.92    (![A:$i,B:$i]:
% 0.65/0.92     ( ( r1_xboole_0 @ A @ B ) =>
% 0.65/0.92       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.65/0.92  thf('23', plain,
% 0.65/0.92      (![X40 : $i, X41 : $i]:
% 0.65/0.92         (((k4_xboole_0 @ (k2_xboole_0 @ X40 @ X41) @ X41) = (X40))
% 0.65/0.92          | ~ (r1_xboole_0 @ X40 @ X41))),
% 0.65/0.92      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.65/0.92  thf('24', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf(t40_xboole_1, axiom,
% 0.65/0.92    (![A:$i,B:$i]:
% 0.65/0.92     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.65/0.92  thf('25', plain,
% 0.65/0.92      (![X27 : $i, X28 : $i]:
% 0.65/0.92         ((k4_xboole_0 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 0.65/0.92           = (k4_xboole_0 @ X27 @ X28))),
% 0.65/0.92      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.65/0.92  thf('26', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('27', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('28', plain,
% 0.65/0.92      (![X27 : $i, X28 : $i]:
% 0.65/0.92         ((k6_subset_1 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 0.65/0.92           = (k6_subset_1 @ X27 @ X28))),
% 0.65/0.92      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.65/0.92  thf('29', plain,
% 0.65/0.92      (![X40 : $i, X41 : $i]:
% 0.65/0.92         (((k6_subset_1 @ X40 @ X41) = (X40)) | ~ (r1_xboole_0 @ X40 @ X41))),
% 0.65/0.92      inference('demod', [status(thm)], ['23', '24', '28'])).
% 0.65/0.92  thf('30', plain,
% 0.65/0.92      (((k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_C_3))
% 0.65/0.92         = (k6_subset_1 @ sk_A @ sk_B))),
% 0.65/0.92      inference('sup-', [status(thm)], ['22', '29'])).
% 0.65/0.92  thf(idempotence_k3_xboole_0, axiom,
% 0.65/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.65/0.92  thf('31', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.65/0.92      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.65/0.92  thf(t111_xboole_1, axiom,
% 0.65/0.92    (![A:$i,B:$i,C:$i]:
% 0.65/0.92     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.65/0.92       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.65/0.92  thf('32', plain,
% 0.65/0.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.65/0.92         ((k4_xboole_0 @ (k3_xboole_0 @ X16 @ X18) @ (k3_xboole_0 @ X17 @ X18))
% 0.65/0.92           = (k3_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 0.65/0.92      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.65/0.92  thf('33', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('34', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('35', plain,
% 0.65/0.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.65/0.92         ((k6_subset_1 @ (k3_xboole_0 @ X16 @ X18) @ (k3_xboole_0 @ X17 @ X18))
% 0.65/0.92           = (k3_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ X18))),
% 0.65/0.92      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.65/0.92  thf('36', plain,
% 0.65/0.92      (![X0 : $i, X1 : $i]:
% 0.65/0.92         ((k6_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.65/0.92           = (k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['31', '35'])).
% 0.65/0.92  thf('37', plain,
% 0.65/0.92      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.65/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.92  thf('38', plain,
% 0.65/0.92      (![X0 : $i, X1 : $i]:
% 0.65/0.92         ((k6_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.65/0.92           = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 0.65/0.92      inference('demod', [status(thm)], ['36', '37'])).
% 0.65/0.92  thf(t49_xboole_1, axiom,
% 0.65/0.92    (![A:$i,B:$i,C:$i]:
% 0.65/0.92     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.65/0.92       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.65/0.92  thf('39', plain,
% 0.65/0.92      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.65/0.92         ((k3_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X33))
% 0.65/0.92           = (k4_xboole_0 @ (k3_xboole_0 @ X31 @ X32) @ X33))),
% 0.65/0.92      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.65/0.92  thf('40', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('41', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('42', plain,
% 0.65/0.92      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.65/0.92         ((k3_xboole_0 @ X31 @ (k6_subset_1 @ X32 @ X33))
% 0.65/0.92           = (k6_subset_1 @ (k3_xboole_0 @ X31 @ X32) @ X33))),
% 0.65/0.92      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.65/0.92  thf('43', plain,
% 0.65/0.92      (![X0 : $i, X1 : $i]:
% 0.65/0.92         ((k3_xboole_0 @ X1 @ (k6_subset_1 @ X0 @ X0))
% 0.65/0.92           = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 0.65/0.92      inference('demod', [status(thm)], ['38', '42'])).
% 0.65/0.92  thf(commutativity_k2_xboole_0, axiom,
% 0.65/0.92    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.65/0.92  thf('44', plain,
% 0.65/0.92      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.65/0.92      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.65/0.92  thf(t1_boole, axiom,
% 0.65/0.92    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.65/0.92  thf('45', plain, (![X21 : $i]: ((k2_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.65/0.92      inference('cnf', [status(esa)], [t1_boole])).
% 0.65/0.92  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['44', '45'])).
% 0.65/0.92  thf('47', plain,
% 0.65/0.92      (![X27 : $i, X28 : $i]:
% 0.65/0.92         ((k6_subset_1 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 0.65/0.92           = (k6_subset_1 @ X27 @ X28))),
% 0.65/0.92      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.65/0.92  thf('48', plain,
% 0.65/0.92      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k6_subset_1 @ k1_xboole_0 @ X0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['46', '47'])).
% 0.65/0.92  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['44', '45'])).
% 0.65/0.92  thf(t21_xboole_1, axiom,
% 0.65/0.92    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.65/0.92  thf('50', plain,
% 0.65/0.92      (![X22 : $i, X23 : $i]:
% 0.65/0.92         ((k3_xboole_0 @ X22 @ (k2_xboole_0 @ X22 @ X23)) = (X22))),
% 0.65/0.92      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.65/0.92  thf('51', plain,
% 0.65/0.92      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['49', '50'])).
% 0.65/0.92  thf(t100_xboole_1, axiom,
% 0.65/0.92    (![A:$i,B:$i]:
% 0.65/0.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.65/0.92  thf('52', plain,
% 0.65/0.92      (![X14 : $i, X15 : $i]:
% 0.65/0.92         ((k4_xboole_0 @ X14 @ X15)
% 0.65/0.92           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.65/0.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.65/0.92  thf('53', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('54', plain,
% 0.65/0.92      (![X14 : $i, X15 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X14 @ X15)
% 0.65/0.92           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.65/0.92      inference('demod', [status(thm)], ['52', '53'])).
% 0.65/0.92  thf('55', plain,
% 0.65/0.92      (![X0 : $i]:
% 0.65/0.92         ((k6_subset_1 @ k1_xboole_0 @ X0)
% 0.65/0.92           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['51', '54'])).
% 0.65/0.92  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['44', '45'])).
% 0.65/0.92  thf(l98_xboole_1, axiom,
% 0.65/0.92    (![A:$i,B:$i]:
% 0.65/0.92     ( ( k5_xboole_0 @ A @ B ) =
% 0.65/0.92       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.65/0.92  thf('57', plain,
% 0.65/0.92      (![X12 : $i, X13 : $i]:
% 0.65/0.92         ((k5_xboole_0 @ X12 @ X13)
% 0.65/0.92           = (k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ 
% 0.65/0.92              (k3_xboole_0 @ X12 @ X13)))),
% 0.65/0.92      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.65/0.92  thf('58', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('59', plain,
% 0.65/0.92      (![X12 : $i, X13 : $i]:
% 0.65/0.92         ((k5_xboole_0 @ X12 @ X13)
% 0.65/0.92           = (k6_subset_1 @ (k2_xboole_0 @ X12 @ X13) @ 
% 0.65/0.92              (k3_xboole_0 @ X12 @ X13)))),
% 0.65/0.92      inference('demod', [status(thm)], ['57', '58'])).
% 0.65/0.92  thf('60', plain,
% 0.65/0.92      (![X0 : $i]:
% 0.65/0.92         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.65/0.92           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.65/0.92      inference('sup+', [status(thm)], ['56', '59'])).
% 0.65/0.92  thf('61', plain,
% 0.65/0.92      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['49', '50'])).
% 0.65/0.92  thf('62', plain,
% 0.65/0.92      (![X0 : $i]:
% 0.65/0.92         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 0.65/0.92      inference('demod', [status(thm)], ['60', '61'])).
% 0.65/0.92  thf(t3_boole, axiom,
% 0.65/0.92    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.65/0.92  thf('63', plain, (![X26 : $i]: ((k4_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 0.65/0.92      inference('cnf', [status(esa)], [t3_boole])).
% 0.65/0.92  thf('64', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('65', plain, (![X26 : $i]: ((k6_subset_1 @ X26 @ k1_xboole_0) = (X26))),
% 0.65/0.92      inference('demod', [status(thm)], ['63', '64'])).
% 0.65/0.92  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.65/0.92      inference('demod', [status(thm)], ['62', '65'])).
% 0.65/0.92  thf('67', plain,
% 0.65/0.92      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.65/0.92      inference('demod', [status(thm)], ['55', '66'])).
% 0.65/0.92  thf('68', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.65/0.92      inference('demod', [status(thm)], ['48', '67'])).
% 0.65/0.92  thf('69', plain,
% 0.65/0.92      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['49', '50'])).
% 0.65/0.92  thf('70', plain,
% 0.65/0.92      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.65/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.92  thf('71', plain,
% 0.65/0.92      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['69', '70'])).
% 0.65/0.92  thf('72', plain,
% 0.65/0.92      (![X0 : $i, X1 : $i]:
% 0.65/0.92         ((k3_xboole_0 @ X1 @ (k6_subset_1 @ X0 @ X0)) = (k1_xboole_0))),
% 0.65/0.92      inference('sup+', [status(thm)], ['68', '71'])).
% 0.65/0.92  thf('73', plain,
% 0.65/0.92      (![X0 : $i, X1 : $i]:
% 0.65/0.92         ((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 0.65/0.92      inference('demod', [status(thm)], ['43', '72'])).
% 0.65/0.92  thf('74', plain,
% 0.65/0.92      (((k1_xboole_0)
% 0.65/0.92         = (k3_xboole_0 @ (k1_relat_1 @ sk_C_3) @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.65/0.92      inference('sup+', [status(thm)], ['30', '73'])).
% 0.65/0.92  thf('75', plain,
% 0.65/0.92      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.65/0.92         ((k3_xboole_0 @ X31 @ (k6_subset_1 @ X32 @ X33))
% 0.65/0.92           = (k6_subset_1 @ (k3_xboole_0 @ X31 @ X32) @ X33))),
% 0.65/0.92      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.65/0.92  thf('76', plain,
% 0.65/0.92      (![X9 : $i, X10 : $i]:
% 0.65/0.92         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 0.65/0.92      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.65/0.92  thf('77', plain,
% 0.65/0.92      (![X109 : $i, X110 : $i]:
% 0.65/0.92         ((k6_subset_1 @ X109 @ X110) = (k4_xboole_0 @ X109 @ X110))),
% 0.65/0.92      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.65/0.92  thf('78', plain,
% 0.65/0.92      (![X9 : $i, X10 : $i]:
% 0.65/0.92         ((r1_tarski @ X9 @ X10) | ((k6_subset_1 @ X9 @ X10) != (k1_xboole_0)))),
% 0.65/0.92      inference('demod', [status(thm)], ['76', '77'])).
% 0.65/0.92  thf('79', plain,
% 0.65/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.92         (((k3_xboole_0 @ X2 @ (k6_subset_1 @ X1 @ X0)) != (k1_xboole_0))
% 0.65/0.92          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.65/0.92      inference('sup-', [status(thm)], ['75', '78'])).
% 0.65/0.92  thf('80', plain,
% 0.65/0.92      ((((k1_xboole_0) != (k1_xboole_0))
% 0.65/0.92        | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_3) @ sk_A) @ sk_B))),
% 0.65/0.92      inference('sup-', [status(thm)], ['74', '79'])).
% 0.65/0.92  thf('81', plain,
% 0.65/0.92      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.65/0.92      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.65/0.92  thf('82', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_3))),
% 0.65/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.92  thf(t28_xboole_1, axiom,
% 0.65/0.92    (![A:$i,B:$i]:
% 0.65/0.92     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.65/0.92  thf('83', plain,
% 0.65/0.92      (![X24 : $i, X25 : $i]:
% 0.65/0.92         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 0.65/0.92      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.65/0.92  thf('84', plain, (((k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_C_3)) = (sk_A))),
% 0.65/0.92      inference('sup-', [status(thm)], ['82', '83'])).
% 0.65/0.92  thf('85', plain,
% 0.65/0.92      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.65/0.92      inference('demod', [status(thm)], ['80', '81', '84'])).
% 0.65/0.92  thf('86', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.65/0.92      inference('simplify', [status(thm)], ['85'])).
% 0.65/0.92  thf('87', plain, ($false), inference('demod', [status(thm)], ['0', '86'])).
% 0.65/0.92  
% 0.65/0.92  % SZS output end Refutation
% 0.65/0.92  
% 0.76/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
