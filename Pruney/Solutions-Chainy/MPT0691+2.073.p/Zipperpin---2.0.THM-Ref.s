%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PnDRM6P1SZ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:28 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   81 (  98 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   17
%              Number of atoms          :  594 ( 797 expanded)
%              Number of equality atoms :   38 (  39 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k8_relat_1 @ X4 @ X3 )
        = ( k5_relat_1 @ X3 @ ( k6_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k10_relat_1 @ X10 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X14: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k8_relat_1 @ X4 @ X3 )
        = ( k5_relat_1 @ X3 @ ( k6_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X16: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X16 ) )
      = ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X12 ) @ ( k4_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ X21 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 )
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 )
        = ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 )
        = ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['28','29'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('32',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( sk_A
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t163_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) @ ( k9_relat_1 @ ( k4_relat_1 @ B ) @ ( k9_relat_1 @ B @ A ) ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X7 ) @ X8 ) @ ( k9_relat_1 @ ( k4_relat_1 @ X7 ) @ ( k9_relat_1 @ X7 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t163_relat_1])).

thf('36',plain,
    ( ( r1_tarski @ sk_A @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ ( k4_relat_1 @ sk_B ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ ( k9_relat_1 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PnDRM6P1SZ
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:33:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 212 iterations in 0.133s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.40/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.40/0.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.40/0.58  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.40/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.40/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.58  thf(t146_funct_1, conjecture,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.58         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i]:
% 0.40/0.58        ( ( v1_relat_1 @ B ) =>
% 0.40/0.58          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.58            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t123_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i]:
% 0.40/0.58         (((k8_relat_1 @ X4 @ X3) = (k5_relat_1 @ X3 @ (k6_relat_1 @ X4)))
% 0.40/0.58          | ~ (v1_relat_1 @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.40/0.58  thf(t182_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( v1_relat_1 @ B ) =>
% 0.40/0.58           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.40/0.58             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X9 : $i, X10 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X9)
% 0.40/0.58          | ((k1_relat_1 @ (k5_relat_1 @ X10 @ X9))
% 0.40/0.58              = (k10_relat_1 @ X10 @ (k1_relat_1 @ X9)))
% 0.40/0.58          | ~ (v1_relat_1 @ X10))),
% 0.40/0.58      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.40/0.58            = (k10_relat_1 @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X1))))
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf(t71_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.40/0.58       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.40/0.58  thf('4', plain, (![X14 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X14)) = (X14))),
% 0.40/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.40/0.58  thf(fc4_funct_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.40/0.58       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.40/0.58  thf('5', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.40/0.58  thf('6', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1))
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ((k1_relat_1 @ (k8_relat_1 @ X1 @ X0)) = (k10_relat_1 @ X0 @ X1)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['6'])).
% 0.40/0.58  thf(dt_k8_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X1 : $i, X2 : $i]:
% 0.40/0.58         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.40/0.58  thf(t37_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.40/0.58         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X11 : $i]:
% 0.40/0.58         (((k1_relat_1 @ X11) = (k2_relat_1 @ (k4_relat_1 @ X11)))
% 0.40/0.58          | ~ (v1_relat_1 @ X11))),
% 0.40/0.58      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X3 : $i, X4 : $i]:
% 0.40/0.58         (((k8_relat_1 @ X4 @ X3) = (k5_relat_1 @ X3 @ (k6_relat_1 @ X4)))
% 0.40/0.58          | ~ (v1_relat_1 @ X3))),
% 0.40/0.58      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.40/0.58  thf(t72_relat_1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (![X16 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X16)) = (k6_relat_1 @ X16))),
% 0.40/0.58      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.40/0.58  thf(t54_relat_1, axiom,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ A ) =>
% 0.40/0.58       ( ![B:$i]:
% 0.40/0.58         ( ( v1_relat_1 @ B ) =>
% 0.40/0.58           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.40/0.58             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X12 : $i, X13 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X12)
% 0.40/0.58          | ((k4_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.40/0.58              = (k5_relat_1 @ (k4_relat_1 @ X12) @ (k4_relat_1 @ X13)))
% 0.40/0.58          | ~ (v1_relat_1 @ X13))),
% 0.40/0.58      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.40/0.58            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.40/0.58          | ~ (v1_relat_1 @ X1)
% 0.40/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.40/0.58  thf('14', plain, (![X23 : $i]: (v1_relat_1 @ (k6_relat_1 @ X23))),
% 0.40/0.58      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.40/0.58            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.40/0.58          | ~ (v1_relat_1 @ X1))),
% 0.40/0.58      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.58  thf(t94_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      (![X21 : $i, X22 : $i]:
% 0.40/0.58         (((k7_relat_1 @ X22 @ X21) = (k5_relat_1 @ (k6_relat_1 @ X21) @ X22))
% 0.40/0.58          | ~ (v1_relat_1 @ X22))),
% 0.40/0.58      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.40/0.58  thf('17', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k7_relat_1 @ (k4_relat_1 @ X1) @ X0)
% 0.40/0.58            = (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0))))
% 0.40/0.58          | ~ (v1_relat_1 @ X1)
% 0.40/0.58          | ~ (v1_relat_1 @ (k4_relat_1 @ X1)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['15', '16'])).
% 0.40/0.58  thf(dt_k4_relat_1, axiom,
% 0.40/0.58    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X1)
% 0.40/0.58          | ((k7_relat_1 @ (k4_relat_1 @ X1) @ X0)
% 0.40/0.58              = (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))))),
% 0.40/0.58      inference('clc', [status(thm)], ['17', '18'])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k7_relat_1 @ (k4_relat_1 @ X0) @ X1)
% 0.40/0.58            = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['10', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ((k7_relat_1 @ (k4_relat_1 @ X0) @ X1)
% 0.40/0.58              = (k4_relat_1 @ (k8_relat_1 @ X1 @ X0))))),
% 0.40/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.58  thf(t148_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X5 : $i, X6 : $i]:
% 0.40/0.58         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.40/0.58          | ~ (v1_relat_1 @ X5))),
% 0.40/0.58      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 0.40/0.58            = (k9_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 0.40/0.58          | ~ (v1_relat_1 @ X0)
% 0.40/0.58          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['21', '22'])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X0 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X0)
% 0.40/0.58          | ((k2_relat_1 @ (k4_relat_1 @ (k8_relat_1 @ X1 @ X0)))
% 0.40/0.58              = (k9_relat_1 @ (k4_relat_1 @ X0) @ X1)))),
% 0.40/0.58      inference('clc', [status(thm)], ['23', '24'])).
% 0.40/0.58  thf('26', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t91_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.58         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      (![X19 : $i, X20 : $i]:
% 0.40/0.58         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.40/0.58          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 0.40/0.58          | ~ (v1_relat_1 @ X20))),
% 0.40/0.58      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ sk_B)
% 0.40/0.58        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.58  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('30', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf(t90_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.40/0.58         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i]:
% 0.40/0.58         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 0.40/0.58            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 0.40/0.58          | ~ (v1_relat_1 @ X17))),
% 0.40/0.58      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      ((((sk_A) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.40/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['30', '31'])).
% 0.40/0.58  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('34', plain, (((sk_A) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.58  thf(t163_relat_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( v1_relat_1 @ B ) =>
% 0.40/0.58       ( r1_tarski @
% 0.40/0.58         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) @ 
% 0.40/0.58         ( k9_relat_1 @ ( k4_relat_1 @ B ) @ ( k9_relat_1 @ B @ A ) ) ) ))).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (![X7 : $i, X8 : $i]:
% 0.40/0.58         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X7) @ X8) @ 
% 0.40/0.58           (k9_relat_1 @ (k4_relat_1 @ X7) @ (k9_relat_1 @ X7 @ X8)))
% 0.40/0.58          | ~ (v1_relat_1 @ X7))),
% 0.40/0.58      inference('cnf', [status(esa)], [t163_relat_1])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (((r1_tarski @ sk_A @ 
% 0.40/0.58         (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.40/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      ((r1_tarski @ sk_A @ 
% 0.40/0.58        (k9_relat_1 @ (k4_relat_1 @ sk_B) @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['36', '37'])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (((r1_tarski @ sk_A @ 
% 0.40/0.58         (k2_relat_1 @ 
% 0.40/0.58          (k4_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B))))
% 0.40/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['25', '38'])).
% 0.40/0.58  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      ((r1_tarski @ sk_A @ 
% 0.40/0.58        (k2_relat_1 @ 
% 0.40/0.58         (k4_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B))))),
% 0.40/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      (((r1_tarski @ sk_A @ 
% 0.40/0.58         (k1_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B)))
% 0.40/0.58        | ~ (v1_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('sup+', [status(thm)], ['9', '41'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      ((~ (v1_relat_1 @ sk_B)
% 0.40/0.58        | (r1_tarski @ sk_A @ 
% 0.40/0.58           (k1_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['8', '42'])).
% 0.40/0.58  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      ((r1_tarski @ sk_A @ 
% 0.40/0.58        (k1_relat_1 @ (k8_relat_1 @ (k9_relat_1 @ sk_B @ sk_A) @ sk_B)))),
% 0.40/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.40/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['7', '45'])).
% 0.40/0.58  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.40/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.40/0.58  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
