%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.npaIcBbhI3

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:47 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 140 expanded)
%              Number of leaves         :   33 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  650 (1090 expanded)
%              Number of equality atoms :   53 (  91 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X31 ) @ X32 )
      | ( v4_relat_1 @ X31 @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40
        = ( k7_relat_1 @ X40 @ X41 ) )
      | ~ ( v4_relat_1 @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,
    ( ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X36 @ X37 ) )
        = ( k9_relat_1 @ X36 @ X37 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('12',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('14',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k9_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X57 ) @ ( k6_relat_1 @ X56 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X56 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X57 ) @ ( k6_relat_1 @ X56 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X56 @ X57 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('19',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k7_relat_1 @ X48 @ X47 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X47 ) @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X36 @ X37 ) )
        = ( k9_relat_1 @ X36 @ X37 ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X46: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('26',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','27'])).

thf('29',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k7_relat_1 @ X48 @ X47 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X47 ) @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('30',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) )
        = ( k10_relat_1 @ X39 @ ( k1_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('37',plain,(
    ! [X45: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('38',plain,(
    ! [X59: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X59 ) )
      = ( k6_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('39',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v2_funct_1 @ X54 )
      | ( ( k10_relat_1 @ X54 @ X55 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X54 ) @ X55 ) )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('42',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('43',plain,(
    ! [X50: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('44',plain,(
    ! [X58: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('47',plain,(
    ! [X49: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','45','46','47'])).

thf('49',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['28','48'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('50',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X52 @ X51 ) @ X53 )
        = ( k3_xboole_0 @ X51 @ ( k10_relat_1 @ X52 @ X53 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('51',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('52',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X52 @ X51 ) @ X53 )
        = ( k1_setfam_1 @ ( k2_tarski @ X51 @ ( k10_relat_1 @ X52 @ X53 ) ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.npaIcBbhI3
% 0.13/0.36  % Computer   : n015.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 16:55:38 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 349 iterations in 0.215s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.66  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.66  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.47/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.47/0.66  thf(t175_funct_2, conjecture,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.66       ( ![B:$i,C:$i]:
% 0.47/0.66         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.47/0.66           ( ( k10_relat_1 @ A @ C ) =
% 0.47/0.66             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i]:
% 0.47/0.66        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.66          ( ![B:$i,C:$i]:
% 0.47/0.66            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.47/0.66              ( ( k10_relat_1 @ A @ C ) =
% 0.47/0.66                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.47/0.66  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t71_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.47/0.66       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.47/0.66  thf('1', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.47/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.66  thf(d18_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X31 : $i, X32 : $i]:
% 0.47/0.66         (~ (r1_tarski @ (k1_relat_1 @ X31) @ X32)
% 0.47/0.66          | (v4_relat_1 @ X31 @ X32)
% 0.47/0.66          | ~ (v1_relat_1 @ X31))),
% 0.47/0.66      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (r1_tarski @ X0 @ X1)
% 0.47/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.47/0.66          | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.66  thf(fc3_funct_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.66       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.66  thf('4', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.47/0.66      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      ((v4_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)),
% 0.47/0.66      inference('sup-', [status(thm)], ['0', '5'])).
% 0.47/0.66  thf(t209_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.66       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X40 : $i, X41 : $i]:
% 0.47/0.66         (((X40) = (k7_relat_1 @ X40 @ X41))
% 0.47/0.66          | ~ (v4_relat_1 @ X40 @ X41)
% 0.47/0.66          | ~ (v1_relat_1 @ X40))),
% 0.47/0.66      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      ((~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.47/0.66        | ((k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.47/0.66            = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.66  thf('9', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (((k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.47/0.66         = (k7_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.66  thf(t148_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X36 : $i, X37 : $i]:
% 0.47/0.66         (((k2_relat_1 @ (k7_relat_1 @ X36 @ X37)) = (k9_relat_1 @ X36 @ X37))
% 0.47/0.66          | ~ (v1_relat_1 @ X36))),
% 0.47/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      ((((k2_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.47/0.66          = (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))
% 0.47/0.66        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('sup+', [status(thm)], ['10', '11'])).
% 0.47/0.66  thf('13', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.47/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.66  thf('14', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (((k10_relat_1 @ sk_A @ sk_C)
% 0.47/0.66         = (k9_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.47/0.66  thf(t43_funct_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.47/0.66       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X56 : $i, X57 : $i]:
% 0.47/0.66         ((k5_relat_1 @ (k6_relat_1 @ X57) @ (k6_relat_1 @ X56))
% 0.47/0.66           = (k6_relat_1 @ (k3_xboole_0 @ X56 @ X57)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.47/0.66  thf(t12_setfam_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X29 : $i, X30 : $i]:
% 0.47/0.66         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      (![X56 : $i, X57 : $i]:
% 0.47/0.66         ((k5_relat_1 @ (k6_relat_1 @ X57) @ (k6_relat_1 @ X56))
% 0.47/0.66           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X56 @ X57))))),
% 0.47/0.66      inference('demod', [status(thm)], ['16', '17'])).
% 0.47/0.66  thf(t94_relat_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X47 : $i, X48 : $i]:
% 0.47/0.66         (((k7_relat_1 @ X48 @ X47) = (k5_relat_1 @ (k6_relat_1 @ X47) @ X48))
% 0.47/0.66          | ~ (v1_relat_1 @ X48))),
% 0.47/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.47/0.66  thf('20', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.47/0.66            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.47/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['18', '19'])).
% 0.47/0.66  thf('21', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('22', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.47/0.66           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (![X36 : $i, X37 : $i]:
% 0.47/0.66         (((k2_relat_1 @ (k7_relat_1 @ X36 @ X37)) = (k9_relat_1 @ X36 @ X37))
% 0.47/0.66          | ~ (v1_relat_1 @ X36))),
% 0.47/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k2_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.47/0.66            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.47/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['22', '23'])).
% 0.47/0.66  thf('25', plain, (![X46 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X46)) = (X46))),
% 0.47/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.66  thf('26', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.47/0.66           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (((k10_relat_1 @ sk_A @ sk_C)
% 0.47/0.66         = (k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)))),
% 0.47/0.66      inference('demod', [status(thm)], ['15', '27'])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (![X47 : $i, X48 : $i]:
% 0.47/0.66         (((k7_relat_1 @ X48 @ X47) = (k5_relat_1 @ (k6_relat_1 @ X47) @ X48))
% 0.47/0.66          | ~ (v1_relat_1 @ X48))),
% 0.47/0.66      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.47/0.66  thf('30', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.47/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.66  thf(t182_relat_1, axiom,
% 0.47/0.66    (![A:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ A ) =>
% 0.47/0.66       ( ![B:$i]:
% 0.47/0.66         ( ( v1_relat_1 @ B ) =>
% 0.47/0.66           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.47/0.66             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X38 : $i, X39 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ X38)
% 0.47/0.66          | ((k1_relat_1 @ (k5_relat_1 @ X39 @ X38))
% 0.47/0.66              = (k10_relat_1 @ X39 @ (k1_relat_1 @ X38)))
% 0.47/0.66          | ~ (v1_relat_1 @ X39))),
% 0.47/0.66      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.47/0.66            = (k10_relat_1 @ X1 @ X0))
% 0.47/0.66          | ~ (v1_relat_1 @ X1)
% 0.47/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf('33', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.47/0.66            = (k10_relat_1 @ X1 @ X0))
% 0.47/0.66          | ~ (v1_relat_1 @ X1))),
% 0.47/0.66      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.47/0.66            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.47/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.47/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['29', '34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.47/0.66           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['20', '21'])).
% 0.47/0.66  thf('37', plain, (![X45 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.47/0.66      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.66  thf(t67_funct_1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.47/0.66  thf('38', plain,
% 0.47/0.66      (![X59 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X59)) = (k6_relat_1 @ X59))),
% 0.47/0.66      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.47/0.66  thf(t155_funct_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.66       ( ( v2_funct_1 @ B ) =>
% 0.47/0.66         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.47/0.66  thf('39', plain,
% 0.47/0.66      (![X54 : $i, X55 : $i]:
% 0.47/0.66         (~ (v2_funct_1 @ X54)
% 0.47/0.66          | ((k10_relat_1 @ X54 @ X55)
% 0.47/0.66              = (k9_relat_1 @ (k2_funct_1 @ X54) @ X55))
% 0.47/0.66          | ~ (v1_funct_1 @ X54)
% 0.47/0.66          | ~ (v1_relat_1 @ X54))),
% 0.47/0.66      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.47/0.66  thf('40', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.47/0.66            = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.47/0.66          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.47/0.66          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.47/0.66          | ~ (v2_funct_1 @ (k6_relat_1 @ X0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['38', '39'])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.47/0.66           = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.47/0.66      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.47/0.66  thf('42', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('43', plain, (![X50 : $i]: (v1_funct_1 @ (k6_relat_1 @ X50))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.47/0.66  thf('44', plain, (![X58 : $i]: (v2_funct_1 @ (k6_relat_1 @ X58))),
% 0.47/0.66      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((k10_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.47/0.66           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.47/0.66  thf('46', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('47', plain, (![X49 : $i]: (v1_relat_1 @ (k6_relat_1 @ X49))),
% 0.47/0.66      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.66  thf('48', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.47/0.66           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.47/0.66      inference('demod', [status(thm)], ['35', '36', '37', '45', '46', '47'])).
% 0.47/0.66  thf('49', plain,
% 0.47/0.66      (((k10_relat_1 @ sk_A @ sk_C)
% 0.47/0.66         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('demod', [status(thm)], ['28', '48'])).
% 0.47/0.66  thf(t139_funct_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ C ) =>
% 0.47/0.66       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.47/0.66         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.47/0.66  thf('50', plain,
% 0.47/0.66      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.47/0.66         (((k10_relat_1 @ (k7_relat_1 @ X52 @ X51) @ X53)
% 0.47/0.66            = (k3_xboole_0 @ X51 @ (k10_relat_1 @ X52 @ X53)))
% 0.47/0.66          | ~ (v1_relat_1 @ X52))),
% 0.47/0.66      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.47/0.66  thf('51', plain,
% 0.47/0.66      (![X29 : $i, X30 : $i]:
% 0.47/0.66         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.66  thf('52', plain,
% 0.47/0.66      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.47/0.66         (((k10_relat_1 @ (k7_relat_1 @ X52 @ X51) @ X53)
% 0.47/0.66            = (k1_setfam_1 @ (k2_tarski @ X51 @ (k10_relat_1 @ X52 @ X53))))
% 0.47/0.66          | ~ (v1_relat_1 @ X52))),
% 0.47/0.66      inference('demod', [status(thm)], ['50', '51'])).
% 0.47/0.66  thf('53', plain,
% 0.47/0.66      (((k10_relat_1 @ sk_A @ sk_C)
% 0.47/0.66         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('54', plain,
% 0.47/0.66      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.47/0.66          != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))
% 0.47/0.66        | ~ (v1_relat_1 @ sk_A))),
% 0.47/0.66      inference('sup-', [status(thm)], ['52', '53'])).
% 0.47/0.66  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('56', plain,
% 0.47/0.66      (((k10_relat_1 @ sk_A @ sk_C)
% 0.47/0.66         != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))),
% 0.47/0.66      inference('demod', [status(thm)], ['54', '55'])).
% 0.47/0.66  thf('57', plain, ($false),
% 0.47/0.66      inference('simplify_reflect-', [status(thm)], ['49', '56'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
