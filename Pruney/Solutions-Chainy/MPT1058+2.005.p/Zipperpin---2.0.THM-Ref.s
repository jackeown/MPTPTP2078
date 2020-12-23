%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zNTenzvtiJ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:38 EST 2020

% Result     : Theorem 2.35s
% Output     : Refutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 110 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  559 ( 842 expanded)
%              Number of equality atoms :   50 (  73 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k7_relat_1 @ X51 @ X50 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X50 ) @ X51 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X44 @ X43 ) @ X45 )
        = ( k10_relat_1 @ X44 @ ( k10_relat_1 @ X43 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X61: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X61 ) )
      = ( k6_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('3',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v2_funct_1 @ X56 )
      | ( ( k10_relat_1 @ X56 @ X57 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X56 ) @ X57 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k7_relat_1 @ X51 @ X50 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X50 ) @ X51 ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X58: $i,X59: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X59 ) @ ( k6_relat_1 @ X58 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X58 @ X59 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X54: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X41 @ X42 ) )
        = ( k9_relat_1 @ X41 @ X42 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X47: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('13',plain,(
    ! [X54: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X54: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X55: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X60: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X54: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('24',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X46: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('28',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X52 ) @ X53 )
      | ( ( k7_relat_1 @ X52 @ X53 )
        = X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X54: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B )
    = ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X41 @ X42 ) )
        = ( k9_relat_1 @ X41 @ X42 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('34',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X47: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('36',plain,(
    ! [X54: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['25','44','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zNTenzvtiJ
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:01:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.35/2.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.35/2.57  % Solved by: fo/fo7.sh
% 2.35/2.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.35/2.57  % done 3514 iterations in 2.109s
% 2.35/2.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.35/2.57  % SZS output start Refutation
% 2.35/2.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.35/2.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.35/2.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.35/2.57  thf(sk_C_type, type, sk_C: $i).
% 2.35/2.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.35/2.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.35/2.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.35/2.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.35/2.57  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.35/2.57  thf(sk_A_type, type, sk_A: $i).
% 2.35/2.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.35/2.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.35/2.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.35/2.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.35/2.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.35/2.57  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.35/2.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.35/2.57  thf(sk_B_type, type, sk_B: $i).
% 2.35/2.57  thf(t94_relat_1, axiom,
% 2.35/2.57    (![A:$i,B:$i]:
% 2.35/2.57     ( ( v1_relat_1 @ B ) =>
% 2.35/2.57       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.35/2.57  thf('0', plain,
% 2.35/2.57      (![X50 : $i, X51 : $i]:
% 2.35/2.57         (((k7_relat_1 @ X51 @ X50) = (k5_relat_1 @ (k6_relat_1 @ X50) @ X51))
% 2.35/2.57          | ~ (v1_relat_1 @ X51))),
% 2.35/2.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.35/2.57  thf(t181_relat_1, axiom,
% 2.35/2.57    (![A:$i,B:$i]:
% 2.35/2.57     ( ( v1_relat_1 @ B ) =>
% 2.35/2.57       ( ![C:$i]:
% 2.35/2.57         ( ( v1_relat_1 @ C ) =>
% 2.35/2.57           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 2.35/2.57             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 2.35/2.57  thf('1', plain,
% 2.35/2.57      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.35/2.57         (~ (v1_relat_1 @ X43)
% 2.35/2.57          | ((k10_relat_1 @ (k5_relat_1 @ X44 @ X43) @ X45)
% 2.35/2.57              = (k10_relat_1 @ X44 @ (k10_relat_1 @ X43 @ X45)))
% 2.35/2.57          | ~ (v1_relat_1 @ X44))),
% 2.35/2.57      inference('cnf', [status(esa)], [t181_relat_1])).
% 2.35/2.57  thf(t67_funct_1, axiom,
% 2.35/2.57    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 2.35/2.57  thf('2', plain,
% 2.35/2.57      (![X61 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X61)) = (k6_relat_1 @ X61))),
% 2.35/2.57      inference('cnf', [status(esa)], [t67_funct_1])).
% 2.35/2.57  thf(t155_funct_1, axiom,
% 2.35/2.57    (![A:$i,B:$i]:
% 2.35/2.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.35/2.57       ( ( v2_funct_1 @ B ) =>
% 2.35/2.57         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 2.35/2.57  thf('3', plain,
% 2.35/2.57      (![X56 : $i, X57 : $i]:
% 2.35/2.57         (~ (v2_funct_1 @ X56)
% 2.35/2.57          | ((k10_relat_1 @ X56 @ X57)
% 2.35/2.57              = (k9_relat_1 @ (k2_funct_1 @ X56) @ X57))
% 2.35/2.57          | ~ (v1_funct_1 @ X56)
% 2.35/2.57          | ~ (v1_relat_1 @ X56))),
% 2.35/2.57      inference('cnf', [status(esa)], [t155_funct_1])).
% 2.35/2.57  thf('4', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]:
% 2.35/2.57         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 2.35/2.57            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.35/2.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.35/2.57          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 2.35/2.57          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 2.35/2.57      inference('sup+', [status(thm)], ['2', '3'])).
% 2.35/2.57  thf('5', plain,
% 2.35/2.57      (![X50 : $i, X51 : $i]:
% 2.35/2.57         (((k7_relat_1 @ X51 @ X50) = (k5_relat_1 @ (k6_relat_1 @ X50) @ X51))
% 2.35/2.57          | ~ (v1_relat_1 @ X51))),
% 2.35/2.57      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.35/2.57  thf(t43_funct_1, axiom,
% 2.35/2.57    (![A:$i,B:$i]:
% 2.35/2.57     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 2.35/2.57       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.35/2.57  thf('6', plain,
% 2.35/2.57      (![X58 : $i, X59 : $i]:
% 2.35/2.57         ((k5_relat_1 @ (k6_relat_1 @ X59) @ (k6_relat_1 @ X58))
% 2.35/2.57           = (k6_relat_1 @ (k3_xboole_0 @ X58 @ X59)))),
% 2.35/2.57      inference('cnf', [status(esa)], [t43_funct_1])).
% 2.35/2.57  thf('7', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]:
% 2.35/2.57         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.35/2.57            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.35/2.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.35/2.57      inference('sup+', [status(thm)], ['5', '6'])).
% 2.35/2.57  thf(fc3_funct_1, axiom,
% 2.35/2.57    (![A:$i]:
% 2.35/2.57     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.35/2.57       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.35/2.57  thf('8', plain, (![X54 : $i]: (v1_relat_1 @ (k6_relat_1 @ X54))),
% 2.35/2.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.35/2.57  thf('9', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]:
% 2.35/2.57         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 2.35/2.57           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.35/2.57      inference('demod', [status(thm)], ['7', '8'])).
% 2.35/2.57  thf(t148_relat_1, axiom,
% 2.35/2.57    (![A:$i,B:$i]:
% 2.35/2.57     ( ( v1_relat_1 @ B ) =>
% 2.35/2.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.35/2.57  thf('10', plain,
% 2.35/2.57      (![X41 : $i, X42 : $i]:
% 2.35/2.57         (((k2_relat_1 @ (k7_relat_1 @ X41 @ X42)) = (k9_relat_1 @ X41 @ X42))
% 2.35/2.57          | ~ (v1_relat_1 @ X41))),
% 2.35/2.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.35/2.57  thf('11', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]:
% 2.35/2.57         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 2.35/2.57            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 2.35/2.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 2.35/2.57      inference('sup+', [status(thm)], ['9', '10'])).
% 2.35/2.57  thf(t71_relat_1, axiom,
% 2.35/2.57    (![A:$i]:
% 2.35/2.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.35/2.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.35/2.57  thf('12', plain, (![X47 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 2.35/2.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.35/2.57  thf('13', plain, (![X54 : $i]: (v1_relat_1 @ (k6_relat_1 @ X54))),
% 2.35/2.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.35/2.57  thf('14', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]:
% 2.35/2.57         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.35/2.57      inference('demod', [status(thm)], ['11', '12', '13'])).
% 2.35/2.57  thf('15', plain, (![X54 : $i]: (v1_relat_1 @ (k6_relat_1 @ X54))),
% 2.35/2.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.35/2.57  thf('16', plain, (![X55 : $i]: (v1_funct_1 @ (k6_relat_1 @ X55))),
% 2.35/2.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.35/2.57  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.35/2.57  thf('17', plain, (![X60 : $i]: (v2_funct_1 @ (k6_relat_1 @ X60))),
% 2.35/2.57      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.35/2.57  thf('18', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]:
% 2.35/2.57         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k3_xboole_0 @ X0 @ X1))),
% 2.35/2.57      inference('demod', [status(thm)], ['4', '14', '15', '16', '17'])).
% 2.35/2.57  thf('19', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.57         (((k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0)
% 2.35/2.57            = (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 2.35/2.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 2.35/2.57          | ~ (v1_relat_1 @ X1))),
% 2.35/2.57      inference('sup+', [status(thm)], ['1', '18'])).
% 2.35/2.57  thf('20', plain, (![X54 : $i]: (v1_relat_1 @ (k6_relat_1 @ X54))),
% 2.35/2.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.35/2.57  thf('21', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.57         (((k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0)
% 2.35/2.57            = (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))
% 2.35/2.57          | ~ (v1_relat_1 @ X1))),
% 2.35/2.57      inference('demod', [status(thm)], ['19', '20'])).
% 2.35/2.57  thf('22', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.57         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.35/2.57            = (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2)))
% 2.35/2.57          | ~ (v1_relat_1 @ X1)
% 2.35/2.57          | ~ (v1_relat_1 @ X1))),
% 2.35/2.57      inference('sup+', [status(thm)], ['0', '21'])).
% 2.35/2.57  thf('23', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.35/2.57         (~ (v1_relat_1 @ X1)
% 2.35/2.57          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.35/2.57              = (k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))))),
% 2.35/2.57      inference('simplify', [status(thm)], ['22'])).
% 2.35/2.57  thf(t175_funct_2, conjecture,
% 2.35/2.57    (![A:$i]:
% 2.35/2.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.35/2.57       ( ![B:$i,C:$i]:
% 2.35/2.57         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 2.35/2.57           ( ( k10_relat_1 @ A @ C ) =
% 2.35/2.57             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 2.35/2.57  thf(zf_stmt_0, negated_conjecture,
% 2.35/2.57    (~( ![A:$i]:
% 2.35/2.57        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.35/2.57          ( ![B:$i,C:$i]:
% 2.35/2.57            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 2.35/2.57              ( ( k10_relat_1 @ A @ C ) =
% 2.35/2.57                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 2.35/2.57    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 2.35/2.57  thf('24', plain,
% 2.35/2.57      (((k10_relat_1 @ sk_A @ sk_C)
% 2.35/2.57         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 2.35/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.57  thf('25', plain,
% 2.35/2.57      ((((k10_relat_1 @ sk_A @ sk_C)
% 2.35/2.57          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 2.35/2.57        | ~ (v1_relat_1 @ sk_A))),
% 2.35/2.57      inference('sup-', [status(thm)], ['23', '24'])).
% 2.35/2.57  thf('26', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 2.35/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.57  thf('27', plain, (![X46 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 2.35/2.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.35/2.57  thf(t97_relat_1, axiom,
% 2.35/2.57    (![A:$i,B:$i]:
% 2.35/2.57     ( ( v1_relat_1 @ B ) =>
% 2.35/2.57       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.35/2.57         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 2.35/2.57  thf('28', plain,
% 2.35/2.57      (![X52 : $i, X53 : $i]:
% 2.35/2.57         (~ (r1_tarski @ (k1_relat_1 @ X52) @ X53)
% 2.35/2.57          | ((k7_relat_1 @ X52 @ X53) = (X52))
% 2.35/2.57          | ~ (v1_relat_1 @ X52))),
% 2.35/2.57      inference('cnf', [status(esa)], [t97_relat_1])).
% 2.35/2.57  thf('29', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]:
% 2.35/2.57         (~ (r1_tarski @ X0 @ X1)
% 2.35/2.57          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.35/2.57          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 2.35/2.57      inference('sup-', [status(thm)], ['27', '28'])).
% 2.35/2.57  thf('30', plain, (![X54 : $i]: (v1_relat_1 @ (k6_relat_1 @ X54))),
% 2.35/2.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.35/2.57  thf('31', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]:
% 2.35/2.57         (~ (r1_tarski @ X0 @ X1)
% 2.35/2.57          | ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1) = (k6_relat_1 @ X0)))),
% 2.35/2.57      inference('demod', [status(thm)], ['29', '30'])).
% 2.35/2.57  thf('32', plain,
% 2.35/2.57      (((k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)
% 2.35/2.57         = (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))),
% 2.35/2.57      inference('sup-', [status(thm)], ['26', '31'])).
% 2.35/2.57  thf('33', plain,
% 2.35/2.57      (![X41 : $i, X42 : $i]:
% 2.35/2.57         (((k2_relat_1 @ (k7_relat_1 @ X41 @ X42)) = (k9_relat_1 @ X41 @ X42))
% 2.35/2.57          | ~ (v1_relat_1 @ X41))),
% 2.35/2.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.35/2.57  thf('34', plain,
% 2.35/2.57      ((((k2_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))
% 2.35/2.57          = (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))
% 2.35/2.57        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))))),
% 2.35/2.57      inference('sup+', [status(thm)], ['32', '33'])).
% 2.35/2.57  thf('35', plain, (![X47 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X47)) = (X47))),
% 2.35/2.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.35/2.57  thf('36', plain, (![X54 : $i]: (v1_relat_1 @ (k6_relat_1 @ X54))),
% 2.35/2.57      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.35/2.57  thf('37', plain,
% 2.35/2.57      (((k10_relat_1 @ sk_A @ sk_C)
% 2.35/2.57         = (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 2.35/2.57      inference('demod', [status(thm)], ['34', '35', '36'])).
% 2.35/2.57  thf('38', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]:
% 2.35/2.57         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 2.35/2.57      inference('demod', [status(thm)], ['11', '12', '13'])).
% 2.35/2.57  thf(commutativity_k2_tarski, axiom,
% 2.35/2.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.35/2.57  thf('39', plain,
% 2.35/2.57      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 2.35/2.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.35/2.57  thf(t12_setfam_1, axiom,
% 2.35/2.57    (![A:$i,B:$i]:
% 2.35/2.57     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.35/2.57  thf('40', plain,
% 2.35/2.57      (![X37 : $i, X38 : $i]:
% 2.35/2.57         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 2.35/2.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.35/2.57  thf('41', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]:
% 2.35/2.57         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 2.35/2.57      inference('sup+', [status(thm)], ['39', '40'])).
% 2.35/2.57  thf('42', plain,
% 2.35/2.57      (![X37 : $i, X38 : $i]:
% 2.35/2.57         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 2.35/2.57      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.35/2.57  thf('43', plain,
% 2.35/2.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.35/2.57      inference('sup+', [status(thm)], ['41', '42'])).
% 2.35/2.57  thf('44', plain,
% 2.35/2.57      (((k10_relat_1 @ sk_A @ sk_C)
% 2.35/2.57         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 2.35/2.57      inference('demod', [status(thm)], ['37', '38', '43'])).
% 2.35/2.57  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 2.35/2.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.35/2.57  thf('46', plain,
% 2.35/2.57      (((k10_relat_1 @ sk_A @ sk_C) != (k10_relat_1 @ sk_A @ sk_C))),
% 2.35/2.57      inference('demod', [status(thm)], ['25', '44', '45'])).
% 2.35/2.57  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 2.35/2.57  
% 2.35/2.57  % SZS output end Refutation
% 2.35/2.57  
% 2.35/2.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
