%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HcE8qTJPDR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:08 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 153 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  604 (1258 expanded)
%              Number of equality atoms :   52 ( 112 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X35 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X36 @ X35 ) @ X37 )
        = ( k10_relat_1 @ X36 @ ( k10_relat_1 @ X35 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X47 ) @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X47 ) @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k7_relat_1 @ X43 @ X42 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('12',plain,(
    ! [X40: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) )
        = ( k10_relat_1 @ X39 @ ( k1_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','21'])).

thf('23',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X2 ) @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X2 ) @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('27',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ X33 @ ( k3_xboole_0 @ ( k2_relat_1 @ X33 ) @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('28',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('29',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ X33 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X33 ) @ X34 ) ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','20'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) @ X1 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X41: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('34',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','20'])).

thf('41',plain,(
    ! [X44: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['31','32','39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k10_relat_1 @ X2 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['26','42'])).

thf(t139_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_funct_1])).

thf('44',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('46',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HcE8qTJPDR
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.73  % Solved by: fo/fo7.sh
% 0.51/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.73  % done 474 iterations in 0.281s
% 0.51/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.73  % SZS output start Refutation
% 0.51/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.51/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.73  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.51/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.73  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.51/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.73  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.51/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.73  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.51/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.73  thf(t94_relat_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( v1_relat_1 @ B ) =>
% 0.51/0.73       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.51/0.73  thf('0', plain,
% 0.51/0.73      (![X42 : $i, X43 : $i]:
% 0.51/0.73         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.51/0.73          | ~ (v1_relat_1 @ X43))),
% 0.51/0.73      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.51/0.73  thf(t181_relat_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( v1_relat_1 @ B ) =>
% 0.51/0.73       ( ![C:$i]:
% 0.51/0.73         ( ( v1_relat_1 @ C ) =>
% 0.51/0.73           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.51/0.73             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.51/0.73  thf('1', plain,
% 0.51/0.73      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.51/0.73         (~ (v1_relat_1 @ X35)
% 0.51/0.73          | ((k10_relat_1 @ (k5_relat_1 @ X36 @ X35) @ X37)
% 0.51/0.73              = (k10_relat_1 @ X36 @ (k10_relat_1 @ X35 @ X37)))
% 0.51/0.73          | ~ (v1_relat_1 @ X36))),
% 0.51/0.73      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.51/0.73  thf(t43_funct_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.51/0.73       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.73  thf('2', plain,
% 0.51/0.73      (![X46 : $i, X47 : $i]:
% 0.51/0.73         ((k5_relat_1 @ (k6_relat_1 @ X47) @ (k6_relat_1 @ X46))
% 0.51/0.73           = (k6_relat_1 @ (k3_xboole_0 @ X46 @ X47)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.51/0.73  thf(t12_setfam_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.51/0.73  thf('3', plain,
% 0.51/0.73      (![X31 : $i, X32 : $i]:
% 0.51/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.51/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.73  thf('4', plain,
% 0.51/0.73      (![X46 : $i, X47 : $i]:
% 0.51/0.73         ((k5_relat_1 @ (k6_relat_1 @ X47) @ (k6_relat_1 @ X46))
% 0.51/0.73           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X46 @ X47))))),
% 0.51/0.73      inference('demod', [status(thm)], ['2', '3'])).
% 0.51/0.73  thf('5', plain,
% 0.51/0.73      (![X42 : $i, X43 : $i]:
% 0.51/0.73         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.51/0.73          | ~ (v1_relat_1 @ X43))),
% 0.51/0.73      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.51/0.73  thf('6', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.51/0.73            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.51/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['4', '5'])).
% 0.51/0.73  thf(fc3_funct_1, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.51/0.73       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.51/0.73  thf('7', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.51/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.73  thf('8', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.51/0.73           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.51/0.73      inference('demod', [status(thm)], ['6', '7'])).
% 0.51/0.73  thf(t71_relat_1, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.51/0.73       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.51/0.73  thf('9', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.51/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.51/0.73  thf('10', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.51/0.73           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['8', '9'])).
% 0.51/0.73  thf('11', plain,
% 0.51/0.73      (![X42 : $i, X43 : $i]:
% 0.51/0.73         (((k7_relat_1 @ X43 @ X42) = (k5_relat_1 @ (k6_relat_1 @ X42) @ X43))
% 0.51/0.73          | ~ (v1_relat_1 @ X43))),
% 0.51/0.73      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.51/0.73  thf('12', plain, (![X40 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X40)) = (X40))),
% 0.51/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.51/0.73  thf(t182_relat_1, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( v1_relat_1 @ A ) =>
% 0.51/0.73       ( ![B:$i]:
% 0.51/0.73         ( ( v1_relat_1 @ B ) =>
% 0.51/0.73           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.51/0.73             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.51/0.73  thf('13', plain,
% 0.51/0.73      (![X38 : $i, X39 : $i]:
% 0.51/0.73         (~ (v1_relat_1 @ X38)
% 0.51/0.73          | ((k1_relat_1 @ (k5_relat_1 @ X39 @ X38))
% 0.51/0.73              = (k10_relat_1 @ X39 @ (k1_relat_1 @ X38)))
% 0.51/0.73          | ~ (v1_relat_1 @ X39))),
% 0.51/0.73      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.51/0.73  thf('14', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.51/0.73            = (k10_relat_1 @ X1 @ X0))
% 0.51/0.73          | ~ (v1_relat_1 @ X1)
% 0.51/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['12', '13'])).
% 0.51/0.73  thf('15', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.51/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.73  thf('16', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.51/0.73            = (k10_relat_1 @ X1 @ X0))
% 0.51/0.73          | ~ (v1_relat_1 @ X1))),
% 0.51/0.73      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.73  thf('17', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.51/0.73            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.51/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.51/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['11', '16'])).
% 0.51/0.73  thf('18', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.51/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.73  thf('19', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.51/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.73  thf('20', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.51/0.73           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.51/0.73      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.51/0.73  thf('21', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.51/0.73           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['10', '20'])).
% 0.51/0.73  thf('22', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X0) @ X2))
% 0.51/0.73            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.51/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.51/0.73          | ~ (v1_relat_1 @ X1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['1', '21'])).
% 0.51/0.73  thf('23', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.51/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.73  thf('24', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X0) @ X2))
% 0.51/0.73            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.51/0.73          | ~ (v1_relat_1 @ X1))),
% 0.51/0.73      inference('demod', [status(thm)], ['22', '23'])).
% 0.51/0.73  thf('25', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X2) @ X0))
% 0.51/0.73            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.51/0.73          | ~ (v1_relat_1 @ X1)
% 0.51/0.73          | ~ (v1_relat_1 @ X1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['0', '24'])).
% 0.51/0.73  thf('26', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         (~ (v1_relat_1 @ X1)
% 0.51/0.73          | ((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X2) @ X0))
% 0.51/0.73              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 0.51/0.73      inference('simplify', [status(thm)], ['25'])).
% 0.51/0.73  thf(t168_relat_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( v1_relat_1 @ B ) =>
% 0.51/0.73       ( ( k10_relat_1 @ B @ A ) =
% 0.51/0.73         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.51/0.73  thf('27', plain,
% 0.51/0.73      (![X33 : $i, X34 : $i]:
% 0.51/0.73         (((k10_relat_1 @ X33 @ X34)
% 0.51/0.73            = (k10_relat_1 @ X33 @ (k3_xboole_0 @ (k2_relat_1 @ X33) @ X34)))
% 0.51/0.73          | ~ (v1_relat_1 @ X33))),
% 0.51/0.73      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.51/0.73  thf('28', plain,
% 0.51/0.73      (![X31 : $i, X32 : $i]:
% 0.51/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.51/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.73  thf('29', plain,
% 0.51/0.73      (![X33 : $i, X34 : $i]:
% 0.51/0.73         (((k10_relat_1 @ X33 @ X34)
% 0.51/0.73            = (k10_relat_1 @ X33 @ 
% 0.51/0.73               (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X33) @ X34))))
% 0.51/0.73          | ~ (v1_relat_1 @ X33))),
% 0.51/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.51/0.73  thf('30', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.51/0.73           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['10', '20'])).
% 0.51/0.73  thf('31', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (((k1_setfam_1 @ 
% 0.51/0.73            (k2_tarski @ 
% 0.51/0.73             (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ (k6_relat_1 @ X1)) @ X0)) @ 
% 0.51/0.73             X1))
% 0.51/0.73            = (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.51/0.73          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['29', '30'])).
% 0.51/0.73  thf('32', plain, (![X41 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X41)) = (X41))),
% 0.51/0.73      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.51/0.73  thf(t17_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.51/0.73  thf('33', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.51/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.51/0.73  thf('34', plain,
% 0.51/0.73      (![X31 : $i, X32 : $i]:
% 0.51/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.51/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.73  thf('35', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.51/0.73      inference('demod', [status(thm)], ['33', '34'])).
% 0.51/0.73  thf(t28_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.51/0.73  thf('36', plain,
% 0.51/0.73      (![X2 : $i, X3 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.51/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.51/0.73  thf('37', plain,
% 0.51/0.73      (![X31 : $i, X32 : $i]:
% 0.51/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.51/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.73  thf('38', plain,
% 0.51/0.73      (![X2 : $i, X3 : $i]:
% 0.51/0.73         (((k1_setfam_1 @ (k2_tarski @ X2 @ X3)) = (X2))
% 0.51/0.73          | ~ (r1_tarski @ X2 @ X3))),
% 0.51/0.73      inference('demod', [status(thm)], ['36', '37'])).
% 0.51/0.73  thf('39', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k1_setfam_1 @ 
% 0.51/0.73           (k2_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0))
% 0.51/0.73           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['35', '38'])).
% 0.51/0.73  thf('40', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.51/0.73           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['10', '20'])).
% 0.51/0.73  thf('41', plain, (![X44 : $i]: (v1_relat_1 @ (k6_relat_1 @ X44))),
% 0.51/0.73      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.51/0.73  thf('42', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.51/0.73           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.51/0.73      inference('demod', [status(thm)], ['31', '32', '39', '40', '41'])).
% 0.51/0.73  thf('43', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         (((k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.51/0.73            = (k1_setfam_1 @ (k2_tarski @ X1 @ (k10_relat_1 @ X2 @ X0))))
% 0.51/0.73          | ~ (v1_relat_1 @ X2))),
% 0.51/0.73      inference('sup+', [status(thm)], ['26', '42'])).
% 0.51/0.73  thf(t139_funct_1, conjecture,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( v1_relat_1 @ C ) =>
% 0.51/0.73       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.51/0.73         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.51/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.73        ( ( v1_relat_1 @ C ) =>
% 0.51/0.73          ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.51/0.73            ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.51/0.73    inference('cnf.neg', [status(esa)], [t139_funct_1])).
% 0.51/0.73  thf('44', plain,
% 0.51/0.73      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.51/0.73         != (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('45', plain,
% 0.51/0.73      (![X31 : $i, X32 : $i]:
% 0.51/0.73         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.51/0.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.73  thf('46', plain,
% 0.51/0.73      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.51/0.73         != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))))),
% 0.51/0.73      inference('demod', [status(thm)], ['44', '45'])).
% 0.51/0.73  thf('47', plain,
% 0.51/0.73      ((((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.51/0.73          != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))
% 0.51/0.73        | ~ (v1_relat_1 @ sk_C))),
% 0.51/0.73      inference('sup-', [status(thm)], ['43', '46'])).
% 0.51/0.73  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('49', plain,
% 0.51/0.73      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.51/0.73         != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 0.51/0.73      inference('demod', [status(thm)], ['47', '48'])).
% 0.51/0.73  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 0.51/0.73  
% 0.51/0.73  % SZS output end Refutation
% 0.51/0.73  
% 0.51/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
