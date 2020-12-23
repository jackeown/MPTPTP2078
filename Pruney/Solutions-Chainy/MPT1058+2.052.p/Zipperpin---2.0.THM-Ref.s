%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3yNwGgq8e6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:44 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 712 expanded)
%              Number of leaves         :   33 ( 257 expanded)
%              Depth                    :   21
%              Number of atoms          : 1321 (6162 expanded)
%              Number of equality atoms :   94 ( 542 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k3_xboole_0 @ X34 @ ( k10_relat_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k1_setfam_1 @ ( k2_tarski @ X34 @ ( k10_relat_1 @ X35 @ X36 ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X45 ) @ ( k6_relat_1 @ X44 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X45 ) @ ( k6_relat_1 @ X44 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X44 @ X45 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X31 @ X30 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('14',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k1_setfam_1 @ ( k2_tarski @ X34 @ ( k10_relat_1 @ X35 @ X36 ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('26',plain,(
    ! [X28: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X28: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('30',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ X41 @ ( k1_relat_1 @ X42 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X42 @ X41 ) @ X43 )
      | ( r1_tarski @ X41 @ ( k10_relat_1 @ X42 @ X43 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X33: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('36',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['31','32','33','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    | ( ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k1_setfam_1 @ ( k2_tarski @ X34 @ ( k10_relat_1 @ X35 @ X36 ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k9_relat_1 @ X40 @ ( k10_relat_1 @ X40 @ X39 ) )
        = ( k3_xboole_0 @ X39 @ ( k9_relat_1 @ X40 @ ( k1_relat_1 @ X40 ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('50',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k9_relat_1 @ X40 @ ( k10_relat_1 @ X40 @ X39 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X39 @ ( k9_relat_1 @ X40 @ ( k1_relat_1 @ X40 ) ) ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X33: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('55',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ) @ X0 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['46','56'])).

thf('58',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['61'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('63',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ X37 @ ( k2_relat_1 @ X38 ) )
      | ( ( k9_relat_1 @ X38 @ ( k10_relat_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','64'])).

thf('66',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('67',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X27: $i] :
      ( ( ( k10_relat_1 @ X27 @ ( k2_relat_1 @ X27 ) )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X28: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X28 ) )
      = X28 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('71',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('74',plain,(
    ! [X33: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('75',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['65','66','72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['59','78'])).

thf('80',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['45','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('82',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k1_setfam_1 @ ( k2_tarski @ X34 @ ( k10_relat_1 @ X35 @ X36 ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('86',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X35 @ X34 ) @ X36 )
        = ( k1_setfam_1 @ ( k2_tarski @ X34 @ ( k10_relat_1 @ X35 @ X36 ) ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) )
        = ( k6_relat_1 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('106',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('111',plain,(
    ! [X29: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X29 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('114',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['109','112','113','114'])).

thf('116',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['80','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['65','66','72','73','74','75'])).

thf('118',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
      = ( k10_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k10_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['121','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3yNwGgq8e6
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.31/1.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.31/1.51  % Solved by: fo/fo7.sh
% 1.31/1.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.31/1.51  % done 1425 iterations in 1.062s
% 1.31/1.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.31/1.51  % SZS output start Refutation
% 1.31/1.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.31/1.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.31/1.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.31/1.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.31/1.51  thf(sk_C_type, type, sk_C: $i).
% 1.31/1.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.31/1.51  thf(sk_B_type, type, sk_B: $i).
% 1.31/1.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.31/1.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.31/1.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.31/1.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.31/1.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.31/1.51  thf(sk_A_type, type, sk_A: $i).
% 1.31/1.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.31/1.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.31/1.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.31/1.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.31/1.51  thf(t139_funct_1, axiom,
% 1.31/1.51    (![A:$i,B:$i,C:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ C ) =>
% 1.31/1.51       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.31/1.51         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.31/1.51  thf('0', plain,
% 1.31/1.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.31/1.51         (((k10_relat_1 @ (k7_relat_1 @ X35 @ X34) @ X36)
% 1.31/1.51            = (k3_xboole_0 @ X34 @ (k10_relat_1 @ X35 @ X36)))
% 1.31/1.51          | ~ (v1_relat_1 @ X35))),
% 1.31/1.51      inference('cnf', [status(esa)], [t139_funct_1])).
% 1.31/1.51  thf(t12_setfam_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.31/1.51  thf('1', plain,
% 1.31/1.51      (![X21 : $i, X22 : $i]:
% 1.31/1.51         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 1.31/1.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.31/1.51  thf('2', plain,
% 1.31/1.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.31/1.51         (((k10_relat_1 @ (k7_relat_1 @ X35 @ X34) @ X36)
% 1.31/1.51            = (k1_setfam_1 @ (k2_tarski @ X34 @ (k10_relat_1 @ X35 @ X36))))
% 1.31/1.51          | ~ (v1_relat_1 @ X35))),
% 1.31/1.51      inference('demod', [status(thm)], ['0', '1'])).
% 1.31/1.51  thf(t175_funct_2, conjecture,
% 1.31/1.51    (![A:$i]:
% 1.31/1.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.31/1.51       ( ![B:$i,C:$i]:
% 1.31/1.51         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 1.31/1.51           ( ( k10_relat_1 @ A @ C ) =
% 1.31/1.51             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 1.31/1.51  thf(zf_stmt_0, negated_conjecture,
% 1.31/1.51    (~( ![A:$i]:
% 1.31/1.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.31/1.51          ( ![B:$i,C:$i]:
% 1.31/1.51            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 1.31/1.51              ( ( k10_relat_1 @ A @ C ) =
% 1.31/1.51                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 1.31/1.51    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 1.31/1.51  thf('3', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf(t43_funct_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.31/1.51       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.31/1.51  thf('4', plain,
% 1.31/1.51      (![X44 : $i, X45 : $i]:
% 1.31/1.51         ((k5_relat_1 @ (k6_relat_1 @ X45) @ (k6_relat_1 @ X44))
% 1.31/1.51           = (k6_relat_1 @ (k3_xboole_0 @ X44 @ X45)))),
% 1.31/1.51      inference('cnf', [status(esa)], [t43_funct_1])).
% 1.31/1.51  thf('5', plain,
% 1.31/1.51      (![X21 : $i, X22 : $i]:
% 1.31/1.51         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 1.31/1.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.31/1.51  thf('6', plain,
% 1.31/1.51      (![X44 : $i, X45 : $i]:
% 1.31/1.51         ((k5_relat_1 @ (k6_relat_1 @ X45) @ (k6_relat_1 @ X44))
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X44 @ X45))))),
% 1.31/1.51      inference('demod', [status(thm)], ['4', '5'])).
% 1.31/1.51  thf(t94_relat_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ B ) =>
% 1.31/1.51       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.31/1.51  thf('7', plain,
% 1.31/1.51      (![X30 : $i, X31 : $i]:
% 1.31/1.51         (((k7_relat_1 @ X31 @ X30) = (k5_relat_1 @ (k6_relat_1 @ X30) @ X31))
% 1.31/1.51          | ~ (v1_relat_1 @ X31))),
% 1.31/1.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.31/1.51  thf('8', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 1.31/1.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['6', '7'])).
% 1.31/1.51  thf(fc3_funct_1, axiom,
% 1.31/1.51    (![A:$i]:
% 1.31/1.51     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.31/1.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.31/1.51  thf('9', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('10', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.31/1.51      inference('demod', [status(thm)], ['8', '9'])).
% 1.31/1.51  thf('11', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('12', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['10', '11'])).
% 1.31/1.51  thf(t169_relat_1, axiom,
% 1.31/1.51    (![A:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ A ) =>
% 1.31/1.51       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.31/1.51  thf('13', plain,
% 1.31/1.51      (![X27 : $i]:
% 1.31/1.51         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 1.31/1.51          | ~ (v1_relat_1 @ X27))),
% 1.31/1.51      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.31/1.51  thf('14', plain,
% 1.31/1.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.31/1.51         (((k10_relat_1 @ (k7_relat_1 @ X35 @ X34) @ X36)
% 1.31/1.51            = (k1_setfam_1 @ (k2_tarski @ X34 @ (k10_relat_1 @ X35 @ X36))))
% 1.31/1.51          | ~ (v1_relat_1 @ X35))),
% 1.31/1.51      inference('demod', [status(thm)], ['0', '1'])).
% 1.31/1.51  thf(t48_xboole_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.31/1.51  thf('15', plain,
% 1.31/1.51      (![X10 : $i, X11 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.31/1.51           = (k3_xboole_0 @ X10 @ X11))),
% 1.31/1.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.31/1.51  thf('16', plain,
% 1.31/1.51      (![X21 : $i, X22 : $i]:
% 1.31/1.51         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 1.31/1.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.31/1.51  thf('17', plain,
% 1.31/1.51      (![X10 : $i, X11 : $i]:
% 1.31/1.51         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X10 @ X11)))),
% 1.31/1.51      inference('demod', [status(thm)], ['15', '16'])).
% 1.31/1.51  thf(t36_xboole_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.31/1.51  thf('18', plain,
% 1.31/1.51      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.31/1.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.31/1.51  thf('19', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 1.31/1.51      inference('sup+', [status(thm)], ['17', '18'])).
% 1.31/1.51  thf('20', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ X1)
% 1.31/1.51          | ~ (v1_relat_1 @ X2))),
% 1.31/1.51      inference('sup+', [status(thm)], ['14', '19'])).
% 1.31/1.51  thf('21', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X0)
% 1.31/1.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.31/1.51          | ~ (v1_relat_1 @ X1))),
% 1.31/1.51      inference('sup+', [status(thm)], ['13', '20'])).
% 1.31/1.51  thf('22', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.31/1.51          | (r1_tarski @ 
% 1.31/1.51             (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0))),
% 1.31/1.51      inference('sup-', [status(thm)], ['12', '21'])).
% 1.31/1.51  thf('23', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('24', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0)) @ X0)),
% 1.31/1.51      inference('demod', [status(thm)], ['22', '23'])).
% 1.31/1.51  thf('25', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.31/1.51      inference('demod', [status(thm)], ['8', '9'])).
% 1.31/1.51  thf(t71_relat_1, axiom,
% 1.31/1.51    (![A:$i]:
% 1.31/1.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.31/1.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.31/1.51  thf('26', plain, (![X28 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 1.31/1.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.31/1.51  thf('27', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['25', '26'])).
% 1.31/1.51  thf('28', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 1.31/1.51      inference('demod', [status(thm)], ['24', '27'])).
% 1.31/1.51  thf('29', plain, (![X28 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 1.31/1.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.31/1.51  thf(t163_funct_1, axiom,
% 1.31/1.51    (![A:$i,B:$i,C:$i]:
% 1.31/1.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.31/1.51       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 1.31/1.51           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 1.31/1.51         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.31/1.51  thf('30', plain,
% 1.31/1.51      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.31/1.51         (~ (r1_tarski @ X41 @ (k1_relat_1 @ X42))
% 1.31/1.51          | ~ (r1_tarski @ (k9_relat_1 @ X42 @ X41) @ X43)
% 1.31/1.51          | (r1_tarski @ X41 @ (k10_relat_1 @ X42 @ X43))
% 1.31/1.51          | ~ (v1_funct_1 @ X42)
% 1.31/1.51          | ~ (v1_relat_1 @ X42))),
% 1.31/1.51      inference('cnf', [status(esa)], [t163_funct_1])).
% 1.31/1.51  thf('31', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         (~ (r1_tarski @ X1 @ X0)
% 1.31/1.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.31/1.51          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.31/1.51          | (r1_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 1.31/1.51          | ~ (r1_tarski @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2))),
% 1.31/1.51      inference('sup-', [status(thm)], ['29', '30'])).
% 1.31/1.51  thf('32', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('33', plain, (![X33 : $i]: (v1_funct_1 @ (k6_relat_1 @ X33))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf(t148_relat_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ B ) =>
% 1.31/1.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 1.31/1.51  thf('34', plain,
% 1.31/1.51      (![X23 : $i, X24 : $i]:
% 1.31/1.51         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 1.31/1.51          | ~ (v1_relat_1 @ X23))),
% 1.31/1.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.31/1.51  thf('35', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.31/1.51      inference('demod', [status(thm)], ['8', '9'])).
% 1.31/1.51  thf('36', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 1.31/1.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.31/1.51  thf('37', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['35', '36'])).
% 1.31/1.51  thf('38', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51            = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.31/1.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['34', '37'])).
% 1.31/1.51  thf('39', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('40', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.31/1.51      inference('demod', [status(thm)], ['38', '39'])).
% 1.31/1.51  thf('41', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         (~ (r1_tarski @ X1 @ X0)
% 1.31/1.51          | (r1_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 1.31/1.51          | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X2))),
% 1.31/1.51      inference('demod', [status(thm)], ['31', '32', '33', '40'])).
% 1.31/1.51  thf('42', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((r1_tarski @ X0 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.31/1.51          | ~ (r1_tarski @ X0 @ X1))),
% 1.31/1.51      inference('sup-', [status(thm)], ['28', '41'])).
% 1.31/1.51  thf('43', plain,
% 1.31/1.51      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 1.31/1.51        (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['3', '42'])).
% 1.31/1.51  thf(d10_xboole_0, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.31/1.51  thf('44', plain,
% 1.31/1.51      (![X0 : $i, X2 : $i]:
% 1.31/1.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.31/1.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.51  thf('45', plain,
% 1.31/1.51      ((~ (r1_tarski @ 
% 1.31/1.51           (k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 1.31/1.51           (k10_relat_1 @ sk_A @ sk_C))
% 1.31/1.51        | ((k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 1.31/1.51            = (k10_relat_1 @ sk_A @ sk_C)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['43', '44'])).
% 1.31/1.51  thf('46', plain,
% 1.31/1.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.31/1.51         (((k10_relat_1 @ (k7_relat_1 @ X35 @ X34) @ X36)
% 1.31/1.51            = (k1_setfam_1 @ (k2_tarski @ X34 @ (k10_relat_1 @ X35 @ X36))))
% 1.31/1.51          | ~ (v1_relat_1 @ X35))),
% 1.31/1.51      inference('demod', [status(thm)], ['0', '1'])).
% 1.31/1.51  thf('47', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.31/1.51      inference('demod', [status(thm)], ['38', '39'])).
% 1.31/1.51  thf(t148_funct_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.31/1.51       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 1.31/1.51         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 1.31/1.51  thf('48', plain,
% 1.31/1.51      (![X39 : $i, X40 : $i]:
% 1.31/1.51         (((k9_relat_1 @ X40 @ (k10_relat_1 @ X40 @ X39))
% 1.31/1.51            = (k3_xboole_0 @ X39 @ (k9_relat_1 @ X40 @ (k1_relat_1 @ X40))))
% 1.31/1.51          | ~ (v1_funct_1 @ X40)
% 1.31/1.51          | ~ (v1_relat_1 @ X40))),
% 1.31/1.51      inference('cnf', [status(esa)], [t148_funct_1])).
% 1.31/1.51  thf('49', plain,
% 1.31/1.51      (![X21 : $i, X22 : $i]:
% 1.31/1.51         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 1.31/1.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.31/1.51  thf('50', plain,
% 1.31/1.51      (![X39 : $i, X40 : $i]:
% 1.31/1.51         (((k9_relat_1 @ X40 @ (k10_relat_1 @ X40 @ X39))
% 1.31/1.51            = (k1_setfam_1 @ 
% 1.31/1.51               (k2_tarski @ X39 @ (k9_relat_1 @ X40 @ (k1_relat_1 @ X40)))))
% 1.31/1.51          | ~ (v1_funct_1 @ X40)
% 1.31/1.51          | ~ (v1_relat_1 @ X40))),
% 1.31/1.51      inference('demod', [status(thm)], ['48', '49'])).
% 1.31/1.51  thf('51', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 1.31/1.51      inference('sup+', [status(thm)], ['17', '18'])).
% 1.31/1.51  thf('52', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 1.31/1.51          | ~ (v1_relat_1 @ X1)
% 1.31/1.51          | ~ (v1_funct_1 @ X1))),
% 1.31/1.51      inference('sup+', [status(thm)], ['50', '51'])).
% 1.31/1.51  thf('53', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((r1_tarski @ 
% 1.31/1.51           (k1_setfam_1 @ 
% 1.31/1.51            (k2_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 1.31/1.51           X0)
% 1.31/1.51          | ~ (v1_funct_1 @ (k6_relat_1 @ X1))
% 1.31/1.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['47', '52'])).
% 1.31/1.51  thf('54', plain, (![X33 : $i]: (v1_funct_1 @ (k6_relat_1 @ X33))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('55', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('56', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (r1_tarski @ 
% 1.31/1.51          (k1_setfam_1 @ 
% 1.31/1.51           (k2_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))) @ 
% 1.31/1.51          X0)),
% 1.31/1.51      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.31/1.51  thf('57', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((r1_tarski @ 
% 1.31/1.51           (k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0) @ X0)
% 1.31/1.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['46', '56'])).
% 1.31/1.51  thf('58', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('59', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (r1_tarski @ 
% 1.31/1.51          (k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X1) @ X0) @ X0)),
% 1.31/1.51      inference('demod', [status(thm)], ['57', '58'])).
% 1.31/1.51  thf('60', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.31/1.51      inference('demod', [status(thm)], ['38', '39'])).
% 1.31/1.51  thf('61', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.31/1.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.51  thf('62', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.31/1.51      inference('simplify', [status(thm)], ['61'])).
% 1.31/1.51  thf(t147_funct_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.31/1.51       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.31/1.51         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.31/1.51  thf('63', plain,
% 1.31/1.51      (![X37 : $i, X38 : $i]:
% 1.31/1.51         (~ (r1_tarski @ X37 @ (k2_relat_1 @ X38))
% 1.31/1.51          | ((k9_relat_1 @ X38 @ (k10_relat_1 @ X38 @ X37)) = (X37))
% 1.31/1.51          | ~ (v1_funct_1 @ X38)
% 1.31/1.51          | ~ (v1_relat_1 @ X38))),
% 1.31/1.51      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.31/1.51  thf('64', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         (~ (v1_relat_1 @ X0)
% 1.31/1.51          | ~ (v1_funct_1 @ X0)
% 1.31/1.51          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.31/1.51              = (k2_relat_1 @ X0)))),
% 1.31/1.51      inference('sup-', [status(thm)], ['62', '63'])).
% 1.31/1.51  thf('65', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         (((k1_setfam_1 @ 
% 1.31/1.51            (k2_tarski @ X0 @ 
% 1.31/1.51             (k10_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.31/1.51              (k2_relat_1 @ (k6_relat_1 @ X0)))))
% 1.31/1.51            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 1.31/1.51          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.31/1.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['60', '64'])).
% 1.31/1.51  thf('66', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 1.31/1.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.31/1.51  thf('67', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 1.31/1.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.31/1.51  thf('68', plain,
% 1.31/1.51      (![X27 : $i]:
% 1.31/1.51         (((k10_relat_1 @ X27 @ (k2_relat_1 @ X27)) = (k1_relat_1 @ X27))
% 1.31/1.51          | ~ (v1_relat_1 @ X27))),
% 1.31/1.51      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.31/1.51  thf('69', plain,
% 1.31/1.51      (![X0 : $i]:
% 1.31/1.51         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 1.31/1.51            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 1.31/1.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['67', '68'])).
% 1.31/1.51  thf('70', plain, (![X28 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X28)) = (X28))),
% 1.31/1.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.31/1.51  thf('71', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('72', plain,
% 1.31/1.51      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.31/1.51  thf('73', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 1.31/1.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.31/1.51  thf('74', plain, (![X33 : $i]: (v1_funct_1 @ (k6_relat_1 @ X33))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('75', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('76', plain,
% 1.31/1.51      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['65', '66', '72', '73', '74', '75'])).
% 1.31/1.51  thf('77', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.31/1.51      inference('demod', [status(thm)], ['8', '9'])).
% 1.31/1.51  thf('78', plain,
% 1.31/1.51      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['76', '77'])).
% 1.31/1.51  thf('79', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)),
% 1.31/1.51      inference('demod', [status(thm)], ['59', '78'])).
% 1.31/1.51  thf('80', plain,
% 1.31/1.51      (((k10_relat_1 @ (k6_relat_1 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 1.31/1.51         = (k10_relat_1 @ sk_A @ sk_C))),
% 1.31/1.51      inference('demod', [status(thm)], ['45', '79'])).
% 1.31/1.51  thf('81', plain,
% 1.31/1.51      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['69', '70', '71'])).
% 1.31/1.51  thf('82', plain,
% 1.31/1.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.31/1.51         (((k10_relat_1 @ (k7_relat_1 @ X35 @ X34) @ X36)
% 1.31/1.51            = (k1_setfam_1 @ (k2_tarski @ X34 @ (k10_relat_1 @ X35 @ X36))))
% 1.31/1.51          | ~ (v1_relat_1 @ X35))),
% 1.31/1.51      inference('demod', [status(thm)], ['0', '1'])).
% 1.31/1.51  thf('83', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 1.31/1.51            = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.31/1.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['81', '82'])).
% 1.31/1.51  thf('84', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('85', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.31/1.51      inference('demod', [status(thm)], ['83', '84'])).
% 1.31/1.51  thf(t167_relat_1, axiom,
% 1.31/1.51    (![A:$i,B:$i]:
% 1.31/1.51     ( ( v1_relat_1 @ B ) =>
% 1.31/1.51       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.31/1.51  thf('86', plain,
% 1.31/1.51      (![X25 : $i, X26 : $i]:
% 1.31/1.51         ((r1_tarski @ (k10_relat_1 @ X25 @ X26) @ (k1_relat_1 @ X25))
% 1.31/1.51          | ~ (v1_relat_1 @ X25))),
% 1.31/1.51      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.31/1.51  thf('87', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 1.31/1.51           (k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.31/1.51          | ~ (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['85', '86'])).
% 1.31/1.51  thf('88', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['25', '26'])).
% 1.31/1.51  thf('89', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (v1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['10', '11'])).
% 1.31/1.51  thf('90', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 1.31/1.51          (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 1.31/1.51      inference('demod', [status(thm)], ['87', '88', '89'])).
% 1.31/1.51  thf('91', plain,
% 1.31/1.51      (![X0 : $i, X2 : $i]:
% 1.31/1.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.31/1.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.31/1.51  thf('92', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 1.31/1.51             (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))
% 1.31/1.51          | ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 1.31/1.51              = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 1.31/1.51      inference('sup-', [status(thm)], ['90', '91'])).
% 1.31/1.51  thf('93', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 1.31/1.51          (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 1.31/1.51      inference('demod', [status(thm)], ['87', '88', '89'])).
% 1.31/1.51  thf('94', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 1.31/1.51      inference('demod', [status(thm)], ['92', '93'])).
% 1.31/1.51  thf('95', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.31/1.51      inference('demod', [status(thm)], ['8', '9'])).
% 1.31/1.51  thf('96', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['94', '95'])).
% 1.31/1.51  thf('97', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.31/1.51      inference('demod', [status(thm)], ['8', '9'])).
% 1.31/1.51  thf('98', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.31/1.51           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 1.31/1.51      inference('sup+', [status(thm)], ['96', '97'])).
% 1.31/1.51  thf('99', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.31/1.51      inference('demod', [status(thm)], ['83', '84'])).
% 1.31/1.51  thf('100', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k10_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0) @ X0)
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['98', '99'])).
% 1.31/1.51  thf('101', plain,
% 1.31/1.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.31/1.51         (((k10_relat_1 @ (k7_relat_1 @ X35 @ X34) @ X36)
% 1.31/1.51            = (k1_setfam_1 @ (k2_tarski @ X34 @ (k10_relat_1 @ X35 @ X36))))
% 1.31/1.51          | ~ (v1_relat_1 @ X35))),
% 1.31/1.51      inference('demod', [status(thm)], ['0', '1'])).
% 1.31/1.51  thf('102', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.31/1.51      inference('demod', [status(thm)], ['8', '9'])).
% 1.31/1.51  thf('103', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.31/1.51         (((k7_relat_1 @ (k6_relat_1 @ X1) @ (k10_relat_1 @ X2 @ X0))
% 1.31/1.51            = (k6_relat_1 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))
% 1.31/1.51          | ~ (v1_relat_1 @ X2))),
% 1.31/1.51      inference('sup+', [status(thm)], ['101', '102'])).
% 1.31/1.51  thf('104', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (((k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.31/1.51            (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.31/1.51            = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 1.31/1.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['100', '103'])).
% 1.31/1.51  thf('105', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['94', '95'])).
% 1.31/1.51  thf('106', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('107', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X0) @ 
% 1.31/1.51           (k10_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.31/1.51           = (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 1.31/1.51      inference('demod', [status(thm)], ['104', '105', '106'])).
% 1.31/1.51  thf('108', plain,
% 1.31/1.51      (![X23 : $i, X24 : $i]:
% 1.31/1.51         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 1.31/1.51          | ~ (v1_relat_1 @ X23))),
% 1.31/1.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 1.31/1.51  thf('109', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         (((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.31/1.51            = (k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 1.31/1.51               (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.31/1.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['107', '108'])).
% 1.31/1.51  thf('110', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 1.31/1.51           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['94', '95'])).
% 1.31/1.51  thf('111', plain, (![X29 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X29)) = (X29))),
% 1.31/1.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.31/1.51  thf('112', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 1.31/1.51      inference('sup+', [status(thm)], ['110', '111'])).
% 1.31/1.51  thf('113', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.31/1.51           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 1.31/1.51      inference('demod', [status(thm)], ['38', '39'])).
% 1.31/1.51  thf('114', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 1.31/1.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.31/1.51  thf('115', plain,
% 1.31/1.51      (![X0 : $i, X1 : $i]:
% 1.31/1.51         ((k1_setfam_1 @ (k2_tarski @ X0 @ X1))
% 1.31/1.51           = (k1_setfam_1 @ 
% 1.31/1.51              (k2_tarski @ X1 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))))),
% 1.31/1.51      inference('demod', [status(thm)], ['109', '112', '113', '114'])).
% 1.31/1.51  thf('116', plain,
% 1.31/1.51      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 1.31/1.51         = (k1_setfam_1 @ 
% 1.31/1.51            (k2_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 1.31/1.51             (k10_relat_1 @ sk_A @ sk_C))))),
% 1.31/1.51      inference('sup+', [status(thm)], ['80', '115'])).
% 1.31/1.51  thf('117', plain,
% 1.31/1.51      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.31/1.51      inference('demod', [status(thm)], ['65', '66', '72', '73', '74', '75'])).
% 1.31/1.51  thf('118', plain,
% 1.31/1.51      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 1.31/1.51         = (k10_relat_1 @ sk_A @ sk_C))),
% 1.31/1.51      inference('demod', [status(thm)], ['116', '117'])).
% 1.31/1.51  thf('119', plain,
% 1.31/1.51      ((((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 1.31/1.51          = (k10_relat_1 @ sk_A @ sk_C))
% 1.31/1.51        | ~ (v1_relat_1 @ sk_A))),
% 1.31/1.51      inference('sup+', [status(thm)], ['2', '118'])).
% 1.31/1.51  thf('120', plain, ((v1_relat_1 @ sk_A)),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf('121', plain,
% 1.31/1.51      (((k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)
% 1.31/1.51         = (k10_relat_1 @ sk_A @ sk_C))),
% 1.31/1.51      inference('demod', [status(thm)], ['119', '120'])).
% 1.31/1.51  thf('122', plain,
% 1.31/1.51      (((k10_relat_1 @ sk_A @ sk_C)
% 1.31/1.51         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 1.31/1.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.31/1.51  thf('123', plain, ($false),
% 1.31/1.51      inference('simplify_reflect-', [status(thm)], ['121', '122'])).
% 1.31/1.51  
% 1.31/1.51  % SZS output end Refutation
% 1.31/1.51  
% 1.31/1.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
