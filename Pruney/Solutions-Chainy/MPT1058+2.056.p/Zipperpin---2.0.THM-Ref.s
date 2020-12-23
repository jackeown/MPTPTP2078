%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sD1ocJuLUs

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:45 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 224 expanded)
%              Number of leaves         :   29 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  738 (1833 expanded)
%              Number of equality atoms :   58 ( 173 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k7_relat_1 @ X46 @ X45 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X45 ) @ X46 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X60 ) @ ( k6_relat_1 @ X59 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X59 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X59: $i,X60: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X60 ) @ ( k6_relat_1 @ X59 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X59 @ X60 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X39 @ X40 ) )
        = ( k9_relat_1 @ X39 @ X40 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('10',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('11',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ X56 @ ( k1_relat_1 @ X57 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X57 @ X56 ) @ X58 )
      | ( r1_tarski @ X56 @ ( k10_relat_1 @ X57 @ X58 ) )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('21',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X47 ) @ X48 )
      | ( ( k7_relat_1 @ X47 @ X48 )
        = X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,(
    ! [X50: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','18','31','32','33','34'])).

thf('36',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','35'])).

thf('37',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X41 @ X42 ) @ ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ( X0
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k9_relat_1 @ X55 @ ( k10_relat_1 @ X55 @ X54 ) )
        = ( k3_xboole_0 @ X54 @ ( k9_relat_1 @ X55 @ ( k1_relat_1 @ X55 ) ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('47',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k9_relat_1 @ X55 @ ( k10_relat_1 @ X55 @ X54 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X54 @ ( k9_relat_1 @ X55 @ ( k1_relat_1 @ X55 ) ) ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('51',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('53',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('54',plain,(
    ! [X50: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54'])).

thf('56',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['44','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('58',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('59',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X52 @ X51 ) @ X53 )
        = ( k3_xboole_0 @ X51 @ ( k10_relat_1 @ X52 @ X53 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('60',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X52 @ X51 ) @ X53 )
        = ( k1_setfam_1 @ ( k2_tarski @ X51 @ ( k10_relat_1 @ X52 @ X53 ) ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sD1ocJuLUs
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 236 iterations in 0.124s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.60  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.36/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(t175_funct_2, conjecture,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.60       ( ![B:$i,C:$i]:
% 0.36/0.60         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.36/0.60           ( ( k10_relat_1 @ A @ C ) =
% 0.36/0.60             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i]:
% 0.36/0.60        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.60          ( ![B:$i,C:$i]:
% 0.36/0.60            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.36/0.60              ( ( k10_relat_1 @ A @ C ) =
% 0.36/0.60                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.36/0.60  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t94_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      (![X45 : $i, X46 : $i]:
% 0.36/0.60         (((k7_relat_1 @ X46 @ X45) = (k5_relat_1 @ (k6_relat_1 @ X45) @ X46))
% 0.36/0.60          | ~ (v1_relat_1 @ X46))),
% 0.36/0.60      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.36/0.60  thf(t43_funct_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.36/0.60       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (![X59 : $i, X60 : $i]:
% 0.36/0.60         ((k5_relat_1 @ (k6_relat_1 @ X60) @ (k6_relat_1 @ X59))
% 0.36/0.60           = (k6_relat_1 @ (k3_xboole_0 @ X59 @ X60)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.36/0.60  thf(t12_setfam_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (![X37 : $i, X38 : $i]:
% 0.36/0.60         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.36/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      (![X59 : $i, X60 : $i]:
% 0.36/0.60         ((k5_relat_1 @ (k6_relat_1 @ X60) @ (k6_relat_1 @ X59))
% 0.36/0.60           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X59 @ X60))))),
% 0.36/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.36/0.60            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.36/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['1', '4'])).
% 0.36/0.60  thf(fc3_funct_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.36/0.60       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.36/0.60  thf('6', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.36/0.60           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.36/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.60  thf(t148_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.36/0.60  thf('8', plain,
% 0.36/0.60      (![X39 : $i, X40 : $i]:
% 0.36/0.60         (((k2_relat_1 @ (k7_relat_1 @ X39 @ X40)) = (k9_relat_1 @ X39 @ X40))
% 0.36/0.60          | ~ (v1_relat_1 @ X39))),
% 0.36/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.36/0.60  thf('9', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (((k2_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.36/0.60            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.36/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.36/0.60  thf(t71_relat_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.36/0.60       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.36/0.60  thf('10', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.36/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.60  thf('11', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.36/0.60           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.36/0.60  thf(d10_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.36/0.60  thf(t163_funct_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.60       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.36/0.60           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.36/0.60         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X56 @ (k1_relat_1 @ X57))
% 0.36/0.60          | ~ (r1_tarski @ (k9_relat_1 @ X57 @ X56) @ X58)
% 0.36/0.60          | (r1_tarski @ X56 @ (k10_relat_1 @ X57 @ X58))
% 0.36/0.60          | ~ (v1_funct_1 @ X57)
% 0.36/0.60          | ~ (v1_relat_1 @ X57))),
% 0.36/0.60      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X0)
% 0.36/0.60          | ~ (v1_funct_1 @ X0)
% 0.36/0.60          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.36/0.60          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_tarski @ 
% 0.36/0.60             (k1_setfam_1 @ (k2_tarski @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0)))) @ 
% 0.36/0.60             X1)
% 0.36/0.60          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.36/0.60             (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.36/0.60          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.36/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['12', '16'])).
% 0.36/0.60  thf('18', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.36/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.60  thf('19', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.36/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.60  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.36/0.60  thf(t97_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.36/0.60         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      (![X47 : $i, X48 : $i]:
% 0.36/0.60         (~ (r1_tarski @ (k1_relat_1 @ X47) @ X48)
% 0.36/0.60          | ((k7_relat_1 @ X47 @ X48) = (X47))
% 0.36/0.60          | ~ (v1_relat_1 @ X47))),
% 0.36/0.60      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.60  thf('23', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))
% 0.36/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['19', '22'])).
% 0.36/0.60  thf('24', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.36/0.60           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.36/0.60      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.60  thf('27', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))
% 0.36/0.60           = (k6_relat_1 @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.60  thf('28', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.36/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k1_relat_1 @ (k6_relat_1 @ X0))
% 0.36/0.60           = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['27', '28'])).
% 0.36/0.60  thf('30', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.36/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.60  thf('32', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.36/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.60  thf('33', plain, (![X50 : $i]: (v1_funct_1 @ (k6_relat_1 @ X50))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.60  thf('34', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.60  thf('35', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X0 @ X1)
% 0.36/0.60          | (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.36/0.60      inference('demod', [status(thm)], ['17', '18', '31', '32', '33', '34'])).
% 0.36/0.60  thf('36', plain,
% 0.36/0.60      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.36/0.60        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['0', '35'])).
% 0.36/0.60  thf('37', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.36/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.60  thf(t167_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      (![X41 : $i, X42 : $i]:
% 0.36/0.60         ((r1_tarski @ (k10_relat_1 @ X41 @ X42) @ (k1_relat_1 @ X41))
% 0.36/0.60          | ~ (v1_relat_1 @ X41))),
% 0.36/0.60      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 0.36/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.60  thf('40', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.60  thf('41', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 0.36/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.60  thf('42', plain,
% 0.36/0.60      (![X0 : $i, X2 : $i]:
% 0.36/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('43', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.36/0.60          | ((X0) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.60  thf('44', plain,
% 0.36/0.60      (((k10_relat_1 @ sk_A @ sk_C)
% 0.36/0.60         = (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['36', '43'])).
% 0.36/0.60  thf('45', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.36/0.60           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.36/0.60  thf(t148_funct_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.60       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.36/0.60         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.36/0.60  thf('46', plain,
% 0.36/0.60      (![X54 : $i, X55 : $i]:
% 0.36/0.60         (((k9_relat_1 @ X55 @ (k10_relat_1 @ X55 @ X54))
% 0.36/0.60            = (k3_xboole_0 @ X54 @ (k9_relat_1 @ X55 @ (k1_relat_1 @ X55))))
% 0.36/0.60          | ~ (v1_funct_1 @ X55)
% 0.36/0.60          | ~ (v1_relat_1 @ X55))),
% 0.36/0.60      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.36/0.60  thf('47', plain,
% 0.36/0.60      (![X37 : $i, X38 : $i]:
% 0.36/0.60         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.36/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.60  thf('48', plain,
% 0.36/0.60      (![X54 : $i, X55 : $i]:
% 0.36/0.60         (((k9_relat_1 @ X55 @ (k10_relat_1 @ X55 @ X54))
% 0.36/0.60            = (k1_setfam_1 @ 
% 0.36/0.60               (k2_tarski @ X54 @ (k9_relat_1 @ X55 @ (k1_relat_1 @ X55)))))
% 0.36/0.60          | ~ (v1_funct_1 @ X55)
% 0.36/0.60          | ~ (v1_relat_1 @ X55))),
% 0.36/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.60  thf('49', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.36/0.60            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.36/0.60            = (k1_setfam_1 @ 
% 0.36/0.60               (k2_tarski @ X1 @ 
% 0.36/0.60                (k1_setfam_1 @ 
% 0.36/0.60                 (k2_tarski @ X0 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))))
% 0.36/0.60          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.36/0.60          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['45', '48'])).
% 0.36/0.60  thf('50', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.36/0.60           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.36/0.60  thf('51', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.36/0.60      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.60  thf('52', plain,
% 0.36/0.60      (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.60  thf('53', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.60  thf('54', plain, (![X50 : $i]: (v1_funct_1 @ (k6_relat_1 @ X50))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.60  thf('55', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k1_setfam_1 @ 
% 0.36/0.60           (k2_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.36/0.60           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['49', '50', '51', '52', '53', '54'])).
% 0.36/0.60  thf('56', plain,
% 0.36/0.60      (((k1_setfam_1 @ 
% 0.36/0.60         (k2_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.36/0.60         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.36/0.60      inference('sup+', [status(thm)], ['44', '55'])).
% 0.36/0.60  thf('57', plain,
% 0.36/0.60      (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.60  thf('58', plain,
% 0.36/0.60      (((k10_relat_1 @ sk_A @ sk_C)
% 0.36/0.60         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.36/0.60      inference('demod', [status(thm)], ['56', '57'])).
% 0.36/0.60  thf(t139_funct_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ C ) =>
% 0.36/0.60       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.36/0.60         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.36/0.60  thf('59', plain,
% 0.36/0.60      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.36/0.60         (((k10_relat_1 @ (k7_relat_1 @ X52 @ X51) @ X53)
% 0.36/0.60            = (k3_xboole_0 @ X51 @ (k10_relat_1 @ X52 @ X53)))
% 0.36/0.60          | ~ (v1_relat_1 @ X52))),
% 0.36/0.60      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.36/0.60  thf('60', plain,
% 0.36/0.60      (![X37 : $i, X38 : $i]:
% 0.36/0.60         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.36/0.60      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.60  thf('61', plain,
% 0.36/0.60      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.36/0.60         (((k10_relat_1 @ (k7_relat_1 @ X52 @ X51) @ X53)
% 0.36/0.60            = (k1_setfam_1 @ (k2_tarski @ X51 @ (k10_relat_1 @ X52 @ X53))))
% 0.36/0.60          | ~ (v1_relat_1 @ X52))),
% 0.36/0.60      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.60  thf('62', plain,
% 0.36/0.60      (((k10_relat_1 @ sk_A @ sk_C)
% 0.36/0.60         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('63', plain,
% 0.36/0.60      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.36/0.60          != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))
% 0.36/0.60        | ~ (v1_relat_1 @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.60  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('65', plain,
% 0.36/0.60      (((k10_relat_1 @ sk_A @ sk_C)
% 0.36/0.60         != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.36/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.36/0.60  thf('66', plain, ($false),
% 0.36/0.60      inference('simplify_reflect-', [status(thm)], ['58', '65'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
