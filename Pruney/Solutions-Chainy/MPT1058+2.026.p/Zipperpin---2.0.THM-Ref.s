%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HLSqjUFwpG

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:40 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 266 expanded)
%              Number of leaves         :   46 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          : 1125 (1904 expanded)
%              Number of equality atoms :  102 ( 177 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X77: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X77 ) )
      = X77 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X70: $i] :
      ( ( ( k10_relat_1 @ X70 @ ( k2_relat_1 @ X70 ) )
        = ( k1_relat_1 @ X70 ) )
      | ~ ( v1_relat_1 @ X70 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X76: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X76 ) )
      = X76 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

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

thf('6',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C_2 ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_2 ) )
    = sk_B ),
    inference(demod,[status(thm)],['8','9'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( ( k10_relat_1 @ X71 @ ( k2_xboole_0 @ X72 @ X73 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X71 @ X72 ) @ ( k10_relat_1 @ X71 @ X73 ) ) )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( r1_tarski @ X36 @ ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C_2 ) ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_2 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_2 ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_2 ) @ ( k10_relat_1 @ ( k6_relat_1 @ ( k10_relat_1 @ sk_A @ sk_C_2 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X84 ) @ ( k6_relat_1 @ X83 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X83 @ X84 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X68 @ X69 ) )
      = ( k3_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X84 ) @ ( k6_relat_1 @ X83 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X83 @ X84 ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X76: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X76 ) )
      = X76 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X74: $i,X75: $i] :
      ( ~ ( v1_relat_1 @ X74 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X75 @ X74 ) )
        = ( k10_relat_1 @ X75 @ ( k1_relat_1 @ X74 ) ) )
      | ~ ( v1_relat_1 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X76: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X76 ) )
      = X76 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('30',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_2 ) @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['19','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_2 ) ) ) @ ( k10_relat_1 @ sk_A @ sk_C_2 ) )
    | ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_2 ) ) )
      = ( k10_relat_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('36',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X27 @ X28 ) @ X27 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ! [X36: $i,X37: $i] :
      ( r1_tarski @ X36 @ ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('48',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X68 @ X69 ) )
      = ( k3_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('49',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('51',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('52',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X68 @ X69 ) )
      = ( k3_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('53',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X10 ) ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('58',plain,(
    ! [X34: $i,X35: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X34 @ X35 ) @ X35 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['35','60'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('62',plain,(
    ! [X26: $i] :
      ( r1_tarski @ k1_xboole_0 @ X26 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('66',plain,(
    ! [X25: $i] :
      ( ( k3_xboole_0 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('67',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X26: $i] :
      ( r1_tarski @ k1_xboole_0 @ X26 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('73',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['71','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['68','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['65','77'])).

thf('79',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X27 @ X28 ) @ X27 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('83',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X68 @ X69 ) )
      = ( k3_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','87'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('89',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k3_xboole_0 @ X31 @ ( k4_xboole_0 @ X32 @ X33 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X31 @ X32 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('90',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X68 @ X69 ) )
      = ( k3_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('91',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X68 @ X69 ) )
      = ( k3_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('92',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ ( k4_xboole_0 @ X32 @ X33 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) ) @ X33 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['88','92'])).

thf('94',plain,(
    ! [X25: $i] :
      ( ( k3_xboole_0 @ X25 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('95',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X68 @ X69 ) )
      = ( k3_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('96',plain,(
    ! [X25: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X25 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_2 ) ) )
    = ( k10_relat_1 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['34','105'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('107',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X81 @ X80 ) @ X82 )
        = ( k3_xboole_0 @ X80 @ ( k10_relat_1 @ X81 @ X82 ) ) )
      | ~ ( v1_relat_1 @ X81 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('108',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X68 @ X69 ) )
      = ( k3_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('109',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X81 @ X80 ) @ X82 )
        = ( k1_setfam_1 @ ( k2_tarski @ X80 @ ( k10_relat_1 @ X81 @ X82 ) ) ) )
      | ~ ( v1_relat_1 @ X81 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_2 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C_2 )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_2 ) ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_2 )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['106','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HLSqjUFwpG
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:29:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.82/1.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.04  % Solved by: fo/fo7.sh
% 0.82/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.04  % done 1792 iterations in 0.574s
% 0.82/1.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.04  % SZS output start Refutation
% 0.82/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.82/1.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.82/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.04  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.82/1.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.82/1.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.82/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.82/1.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.82/1.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.82/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.04  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.82/1.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.82/1.04  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.82/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.82/1.04  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.82/1.04  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.82/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.82/1.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.82/1.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.82/1.04  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.82/1.04  thf(t71_relat_1, axiom,
% 0.82/1.04    (![A:$i]:
% 0.82/1.04     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.82/1.04       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.82/1.04  thf('0', plain, (![X77 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X77)) = (X77))),
% 0.82/1.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.82/1.04  thf(t169_relat_1, axiom,
% 0.82/1.04    (![A:$i]:
% 0.82/1.04     ( ( v1_relat_1 @ A ) =>
% 0.82/1.04       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.82/1.04  thf('1', plain,
% 0.82/1.04      (![X70 : $i]:
% 0.82/1.04         (((k10_relat_1 @ X70 @ (k2_relat_1 @ X70)) = (k1_relat_1 @ X70))
% 0.82/1.04          | ~ (v1_relat_1 @ X70))),
% 0.82/1.04      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.82/1.04  thf('2', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.82/1.04            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.82/1.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['0', '1'])).
% 0.82/1.04  thf('3', plain, (![X76 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X76)) = (X76))),
% 0.82/1.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.82/1.04  thf(fc3_funct_1, axiom,
% 0.82/1.04    (![A:$i]:
% 0.82/1.04     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.82/1.04       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.82/1.04  thf('4', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 0.82/1.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.82/1.04  thf('5', plain,
% 0.82/1.04      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.82/1.04      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.82/1.04  thf(t175_funct_2, conjecture,
% 0.82/1.04    (![A:$i]:
% 0.82/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.04       ( ![B:$i,C:$i]:
% 0.82/1.04         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.82/1.04           ( ( k10_relat_1 @ A @ C ) =
% 0.82/1.04             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.82/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.82/1.04    (~( ![A:$i]:
% 0.82/1.04        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.82/1.04          ( ![B:$i,C:$i]:
% 0.82/1.04            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.82/1.04              ( ( k10_relat_1 @ A @ C ) =
% 0.82/1.04                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.82/1.04    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.82/1.04  thf('6', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_2) @ sk_B)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf(t12_xboole_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.82/1.04  thf('7', plain,
% 0.82/1.04      (![X16 : $i, X17 : $i]:
% 0.82/1.04         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.82/1.04  thf('8', plain,
% 0.82/1.04      (((k2_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C_2) @ sk_B) = (sk_B))),
% 0.82/1.04      inference('sup-', [status(thm)], ['6', '7'])).
% 0.82/1.04  thf(commutativity_k2_xboole_0, axiom,
% 0.82/1.04    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.82/1.04  thf('9', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.04  thf('10', plain,
% 0.82/1.04      (((k2_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_2)) = (sk_B))),
% 0.82/1.04      inference('demod', [status(thm)], ['8', '9'])).
% 0.82/1.04  thf(t175_relat_1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( v1_relat_1 @ C ) =>
% 0.82/1.04       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.82/1.04         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.82/1.04  thf('11', plain,
% 0.82/1.04      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.82/1.04         (((k10_relat_1 @ X71 @ (k2_xboole_0 @ X72 @ X73))
% 0.82/1.04            = (k2_xboole_0 @ (k10_relat_1 @ X71 @ X72) @ 
% 0.82/1.04               (k10_relat_1 @ X71 @ X73)))
% 0.82/1.04          | ~ (v1_relat_1 @ X71))),
% 0.82/1.04      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.82/1.04  thf('12', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.04  thf(t7_xboole_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.82/1.04  thf('13', plain,
% 0.82/1.04      (![X36 : $i, X37 : $i]: (r1_tarski @ X36 @ (k2_xboole_0 @ X36 @ X37))),
% 0.82/1.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.82/1.04  thf('14', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['12', '13'])).
% 0.82/1.04  thf('15', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.04         ((r1_tarski @ (k10_relat_1 @ X2 @ X0) @ 
% 0.82/1.04           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.82/1.04          | ~ (v1_relat_1 @ X2))),
% 0.82/1.04      inference('sup+', [status(thm)], ['11', '14'])).
% 0.82/1.04  thf('16', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         ((r1_tarski @ (k10_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C_2)) @ 
% 0.82/1.04           (k10_relat_1 @ X0 @ sk_B))
% 0.82/1.04          | ~ (v1_relat_1 @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['10', '15'])).
% 0.82/1.04  thf('17', plain,
% 0.82/1.04      (((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_2) @ 
% 0.82/1.04         (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_2)) @ sk_B))
% 0.82/1.04        | ~ (v1_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_2))))),
% 0.82/1.04      inference('sup+', [status(thm)], ['5', '16'])).
% 0.82/1.04  thf('18', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 0.82/1.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.82/1.04  thf('19', plain,
% 0.82/1.04      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_2) @ 
% 0.82/1.04        (k10_relat_1 @ (k6_relat_1 @ (k10_relat_1 @ sk_A @ sk_C_2)) @ sk_B))),
% 0.82/1.04      inference('demod', [status(thm)], ['17', '18'])).
% 0.82/1.04  thf(t43_funct_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.82/1.04       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.82/1.04  thf('20', plain,
% 0.82/1.04      (![X83 : $i, X84 : $i]:
% 0.82/1.04         ((k5_relat_1 @ (k6_relat_1 @ X84) @ (k6_relat_1 @ X83))
% 0.82/1.04           = (k6_relat_1 @ (k3_xboole_0 @ X83 @ X84)))),
% 0.82/1.04      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.82/1.04  thf(t12_setfam_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.82/1.04  thf('21', plain,
% 0.82/1.04      (![X68 : $i, X69 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X68 @ X69)) = (k3_xboole_0 @ X68 @ X69))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.82/1.04  thf('22', plain,
% 0.82/1.04      (![X83 : $i, X84 : $i]:
% 0.82/1.04         ((k5_relat_1 @ (k6_relat_1 @ X84) @ (k6_relat_1 @ X83))
% 0.82/1.04           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X83 @ X84))))),
% 0.82/1.04      inference('demod', [status(thm)], ['20', '21'])).
% 0.82/1.04  thf('23', plain, (![X76 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X76)) = (X76))),
% 0.82/1.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.82/1.04  thf(t182_relat_1, axiom,
% 0.82/1.04    (![A:$i]:
% 0.82/1.04     ( ( v1_relat_1 @ A ) =>
% 0.82/1.04       ( ![B:$i]:
% 0.82/1.04         ( ( v1_relat_1 @ B ) =>
% 0.82/1.04           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.82/1.04             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.82/1.04  thf('24', plain,
% 0.82/1.04      (![X74 : $i, X75 : $i]:
% 0.82/1.04         (~ (v1_relat_1 @ X74)
% 0.82/1.04          | ((k1_relat_1 @ (k5_relat_1 @ X75 @ X74))
% 0.82/1.04              = (k10_relat_1 @ X75 @ (k1_relat_1 @ X74)))
% 0.82/1.04          | ~ (v1_relat_1 @ X75))),
% 0.82/1.04      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.82/1.04  thf('25', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.82/1.04            = (k10_relat_1 @ X1 @ X0))
% 0.82/1.04          | ~ (v1_relat_1 @ X1)
% 0.82/1.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['23', '24'])).
% 0.82/1.04  thf('26', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 0.82/1.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.82/1.04  thf('27', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.82/1.04            = (k10_relat_1 @ X1 @ X0))
% 0.82/1.04          | ~ (v1_relat_1 @ X1))),
% 0.82/1.04      inference('demod', [status(thm)], ['25', '26'])).
% 0.82/1.04  thf('28', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         (((k1_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.82/1.04            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.82/1.04          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['22', '27'])).
% 0.82/1.04  thf('29', plain, (![X76 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X76)) = (X76))),
% 0.82/1.04      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.82/1.04  thf('30', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 0.82/1.04      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.82/1.04  thf('31', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.82/1.04           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.82/1.04      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.82/1.04  thf('32', plain,
% 0.82/1.04      ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_2) @ 
% 0.82/1.04        (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_2))))),
% 0.82/1.04      inference('demod', [status(thm)], ['19', '31'])).
% 0.82/1.04  thf(d10_xboole_0, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.82/1.04  thf('33', plain,
% 0.82/1.04      (![X11 : $i, X13 : $i]:
% 0.82/1.04         (((X11) = (X13))
% 0.82/1.04          | ~ (r1_tarski @ X13 @ X11)
% 0.82/1.04          | ~ (r1_tarski @ X11 @ X13))),
% 0.82/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.82/1.04  thf('34', plain,
% 0.82/1.04      ((~ (r1_tarski @ 
% 0.82/1.04           (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_2))) @ 
% 0.82/1.04           (k10_relat_1 @ sk_A @ sk_C_2))
% 0.82/1.04        | ((k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_2)))
% 0.82/1.04            = (k10_relat_1 @ sk_A @ sk_C_2)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['32', '33'])).
% 0.82/1.04  thf(d3_tarski, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( r1_tarski @ A @ B ) <=>
% 0.82/1.04       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.82/1.04  thf('35', plain,
% 0.82/1.04      (![X3 : $i, X5 : $i]:
% 0.82/1.04         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.82/1.04      inference('cnf', [status(esa)], [d3_tarski])).
% 0.82/1.04  thf(idempotence_k3_xboole_0, axiom,
% 0.82/1.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.82/1.04  thf('36', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.82/1.04      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.82/1.04  thf(t100_xboole_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.82/1.04  thf('37', plain,
% 0.82/1.04      (![X14 : $i, X15 : $i]:
% 0.82/1.04         ((k4_xboole_0 @ X14 @ X15)
% 0.82/1.04           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.82/1.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.82/1.04  thf('38', plain,
% 0.82/1.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['36', '37'])).
% 0.82/1.04  thf(t36_xboole_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.82/1.04  thf('39', plain,
% 0.82/1.04      (![X27 : $i, X28 : $i]: (r1_tarski @ (k4_xboole_0 @ X27 @ X28) @ X27)),
% 0.82/1.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.82/1.04  thf('40', plain, (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.82/1.04      inference('sup+', [status(thm)], ['38', '39'])).
% 0.82/1.04  thf('41', plain,
% 0.82/1.04      (![X16 : $i, X17 : $i]:
% 0.82/1.04         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.82/1.04  thf('42', plain,
% 0.82/1.04      (![X0 : $i]: ((k2_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.82/1.04      inference('sup-', [status(thm)], ['40', '41'])).
% 0.82/1.04  thf('43', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.04  thf('44', plain,
% 0.82/1.04      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.82/1.04      inference('demod', [status(thm)], ['42', '43'])).
% 0.82/1.04  thf('45', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.04  thf('46', plain,
% 0.82/1.04      (![X36 : $i, X37 : $i]: (r1_tarski @ X36 @ (k2_xboole_0 @ X36 @ X37))),
% 0.82/1.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.82/1.04  thf(t28_xboole_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.82/1.04  thf('47', plain,
% 0.82/1.04      (![X23 : $i, X24 : $i]:
% 0.82/1.04         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.82/1.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.82/1.04  thf('48', plain,
% 0.82/1.04      (![X68 : $i, X69 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X68 @ X69)) = (k3_xboole_0 @ X68 @ X69))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.82/1.04  thf('49', plain,
% 0.82/1.04      (![X23 : $i, X24 : $i]:
% 0.82/1.04         (((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (X23))
% 0.82/1.04          | ~ (r1_tarski @ X23 @ X24))),
% 0.82/1.04      inference('demod', [status(thm)], ['47', '48'])).
% 0.82/1.04  thf('50', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))) = (X1))),
% 0.82/1.04      inference('sup-', [status(thm)], ['46', '49'])).
% 0.82/1.04  thf(t4_xboole_0, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.82/1.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.82/1.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.82/1.04            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.82/1.04  thf('51', plain,
% 0.82/1.04      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.82/1.04          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.82/1.04      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.82/1.04  thf('52', plain,
% 0.82/1.04      (![X68 : $i, X69 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X68 @ X69)) = (k3_xboole_0 @ X68 @ X69))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.82/1.04  thf('53', plain,
% 0.82/1.04      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X9 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X10)))
% 0.82/1.04          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.82/1.04      inference('demod', [status(thm)], ['51', '52'])).
% 0.82/1.04  thf('54', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.04         (~ (r2_hidden @ X2 @ X0)
% 0.82/1.04          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['50', '53'])).
% 0.82/1.04  thf('55', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.04         (~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.82/1.04          | ~ (r2_hidden @ X2 @ X0))),
% 0.82/1.04      inference('sup-', [status(thm)], ['45', '54'])).
% 0.82/1.04  thf('56', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         (~ (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)
% 0.82/1.04          | ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['44', '55'])).
% 0.82/1.04  thf('57', plain,
% 0.82/1.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['36', '37'])).
% 0.82/1.04  thf(t79_xboole_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.82/1.04  thf('58', plain,
% 0.82/1.04      (![X34 : $i, X35 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X34 @ X35) @ X35)),
% 0.82/1.04      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.82/1.04  thf('59', plain, (![X0 : $i]: (r1_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X0)),
% 0.82/1.04      inference('sup+', [status(thm)], ['57', '58'])).
% 0.82/1.04  thf('60', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.82/1.04      inference('demod', [status(thm)], ['56', '59'])).
% 0.82/1.04  thf('61', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ X0) @ X1)),
% 0.82/1.04      inference('sup-', [status(thm)], ['35', '60'])).
% 0.82/1.04  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.82/1.04  thf('62', plain, (![X26 : $i]: (r1_tarski @ k1_xboole_0 @ X26)),
% 0.82/1.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.82/1.04  thf('63', plain,
% 0.82/1.04      (![X11 : $i, X13 : $i]:
% 0.82/1.04         (((X11) = (X13))
% 0.82/1.04          | ~ (r1_tarski @ X13 @ X11)
% 0.82/1.04          | ~ (r1_tarski @ X11 @ X13))),
% 0.82/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.82/1.04  thf('64', plain,
% 0.82/1.04      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.82/1.04      inference('sup-', [status(thm)], ['62', '63'])).
% 0.82/1.04  thf('65', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.82/1.04      inference('sup-', [status(thm)], ['61', '64'])).
% 0.82/1.04  thf(t2_boole, axiom,
% 0.82/1.04    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.82/1.04  thf('66', plain,
% 0.82/1.04      (![X25 : $i]: ((k3_xboole_0 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.04      inference('cnf', [status(esa)], [t2_boole])).
% 0.82/1.04  thf('67', plain,
% 0.82/1.04      (![X14 : $i, X15 : $i]:
% 0.82/1.04         ((k4_xboole_0 @ X14 @ X15)
% 0.82/1.04           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.82/1.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.82/1.04  thf('68', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['66', '67'])).
% 0.82/1.04  thf('69', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['66', '67'])).
% 0.82/1.04  thf(t39_xboole_1, axiom,
% 0.82/1.04    (![A:$i,B:$i]:
% 0.82/1.04     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.82/1.04  thf('70', plain,
% 0.82/1.04      (![X29 : $i, X30 : $i]:
% 0.82/1.04         ((k2_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29))
% 0.82/1.04           = (k2_xboole_0 @ X29 @ X30))),
% 0.82/1.04      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.82/1.04  thf('71', plain,
% 0.82/1.04      (![X0 : $i]:
% 0.82/1.04         ((k2_xboole_0 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.82/1.04           = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['69', '70'])).
% 0.82/1.04  thf('72', plain, (![X26 : $i]: (r1_tarski @ k1_xboole_0 @ X26)),
% 0.82/1.04      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.82/1.04  thf('73', plain,
% 0.82/1.04      (![X16 : $i, X17 : $i]:
% 0.82/1.04         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.82/1.04  thf('74', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.04      inference('sup-', [status(thm)], ['72', '73'])).
% 0.82/1.04  thf('75', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.04      inference('sup-', [status(thm)], ['72', '73'])).
% 0.82/1.04  thf('76', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.82/1.04      inference('demod', [status(thm)], ['71', '74', '75'])).
% 0.82/1.04  thf('77', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.82/1.04      inference('demod', [status(thm)], ['68', '76'])).
% 0.82/1.04  thf('78', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.82/1.04      inference('sup+', [status(thm)], ['65', '77'])).
% 0.82/1.04  thf('79', plain,
% 0.82/1.04      (![X27 : $i, X28 : $i]: (r1_tarski @ (k4_xboole_0 @ X27 @ X28) @ X27)),
% 0.82/1.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.82/1.04  thf('80', plain,
% 0.82/1.04      (![X23 : $i, X24 : $i]:
% 0.82/1.04         (((k1_setfam_1 @ (k2_tarski @ X23 @ X24)) = (X23))
% 0.82/1.04          | ~ (r1_tarski @ X23 @ X24))),
% 0.82/1.04      inference('demod', [status(thm)], ['47', '48'])).
% 0.82/1.04  thf('81', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 0.82/1.04           = (k4_xboole_0 @ X0 @ X1))),
% 0.82/1.04      inference('sup-', [status(thm)], ['79', '80'])).
% 0.82/1.04  thf('82', plain,
% 0.82/1.04      (![X14 : $i, X15 : $i]:
% 0.82/1.04         ((k4_xboole_0 @ X14 @ X15)
% 0.82/1.04           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.82/1.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.82/1.04  thf('83', plain,
% 0.82/1.04      (![X68 : $i, X69 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X68 @ X69)) = (k3_xboole_0 @ X68 @ X69))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.82/1.04  thf('84', plain,
% 0.82/1.04      (![X14 : $i, X15 : $i]:
% 0.82/1.04         ((k4_xboole_0 @ X14 @ X15)
% 0.82/1.04           = (k5_xboole_0 @ X14 @ (k1_setfam_1 @ (k2_tarski @ X14 @ X15))))),
% 0.82/1.04      inference('demod', [status(thm)], ['82', '83'])).
% 0.82/1.04  thf('85', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.82/1.04           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.82/1.04      inference('sup+', [status(thm)], ['81', '84'])).
% 0.82/1.04  thf('86', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.82/1.04      inference('sup-', [status(thm)], ['61', '64'])).
% 0.82/1.04  thf('87', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.82/1.04      inference('demod', [status(thm)], ['85', '86'])).
% 0.82/1.04  thf('88', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['78', '87'])).
% 0.82/1.04  thf(t49_xboole_1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.82/1.04       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.82/1.04  thf('89', plain,
% 0.82/1.04      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.82/1.04         ((k3_xboole_0 @ X31 @ (k4_xboole_0 @ X32 @ X33))
% 0.82/1.04           = (k4_xboole_0 @ (k3_xboole_0 @ X31 @ X32) @ X33))),
% 0.82/1.04      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.82/1.04  thf('90', plain,
% 0.82/1.04      (![X68 : $i, X69 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X68 @ X69)) = (k3_xboole_0 @ X68 @ X69))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.82/1.04  thf('91', plain,
% 0.82/1.04      (![X68 : $i, X69 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X68 @ X69)) = (k3_xboole_0 @ X68 @ X69))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.82/1.04  thf('92', plain,
% 0.82/1.04      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X31 @ (k4_xboole_0 @ X32 @ X33)))
% 0.82/1.04           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X31 @ X32)) @ X33))),
% 0.82/1.04      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.82/1.04  thf('93', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X1 @ k1_xboole_0))
% 0.82/1.04           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['88', '92'])).
% 0.82/1.04  thf('94', plain,
% 0.82/1.04      (![X25 : $i]: ((k3_xboole_0 @ X25 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.04      inference('cnf', [status(esa)], [t2_boole])).
% 0.82/1.04  thf('95', plain,
% 0.82/1.04      (![X68 : $i, X69 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X68 @ X69)) = (k3_xboole_0 @ X68 @ X69))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.82/1.04  thf('96', plain,
% 0.82/1.04      (![X25 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X25 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.82/1.04      inference('demod', [status(thm)], ['94', '95'])).
% 0.82/1.04  thf('97', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k1_xboole_0)
% 0.82/1.04           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0))),
% 0.82/1.04      inference('demod', [status(thm)], ['93', '96'])).
% 0.82/1.04  thf('98', plain,
% 0.82/1.04      (![X29 : $i, X30 : $i]:
% 0.82/1.04         ((k2_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29))
% 0.82/1.04           = (k2_xboole_0 @ X29 @ X30))),
% 0.82/1.04      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.82/1.04  thf('99', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.82/1.04           = (k2_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.82/1.04      inference('sup+', [status(thm)], ['97', '98'])).
% 0.82/1.04  thf('100', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.82/1.04      inference('sup-', [status(thm)], ['72', '73'])).
% 0.82/1.04  thf('101', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.82/1.04      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.82/1.04  thf('102', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['100', '101'])).
% 0.82/1.04  thf('103', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         ((X0) = (k2_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.82/1.04      inference('demod', [status(thm)], ['99', '102'])).
% 0.82/1.04  thf('104', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.82/1.04      inference('sup+', [status(thm)], ['12', '13'])).
% 0.82/1.04  thf('105', plain,
% 0.82/1.04      (![X0 : $i, X1 : $i]:
% 0.82/1.04         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.82/1.04      inference('sup+', [status(thm)], ['103', '104'])).
% 0.82/1.04  thf('106', plain,
% 0.82/1.04      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_2)))
% 0.82/1.04         = (k10_relat_1 @ sk_A @ sk_C_2))),
% 0.82/1.04      inference('demod', [status(thm)], ['34', '105'])).
% 0.82/1.04  thf(t139_funct_1, axiom,
% 0.82/1.04    (![A:$i,B:$i,C:$i]:
% 0.82/1.04     ( ( v1_relat_1 @ C ) =>
% 0.82/1.04       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.82/1.04         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.82/1.04  thf('107', plain,
% 0.82/1.04      (![X80 : $i, X81 : $i, X82 : $i]:
% 0.82/1.04         (((k10_relat_1 @ (k7_relat_1 @ X81 @ X80) @ X82)
% 0.82/1.04            = (k3_xboole_0 @ X80 @ (k10_relat_1 @ X81 @ X82)))
% 0.82/1.04          | ~ (v1_relat_1 @ X81))),
% 0.82/1.04      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.82/1.04  thf('108', plain,
% 0.82/1.04      (![X68 : $i, X69 : $i]:
% 0.82/1.04         ((k1_setfam_1 @ (k2_tarski @ X68 @ X69)) = (k3_xboole_0 @ X68 @ X69))),
% 0.82/1.04      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.82/1.04  thf('109', plain,
% 0.82/1.04      (![X80 : $i, X81 : $i, X82 : $i]:
% 0.82/1.04         (((k10_relat_1 @ (k7_relat_1 @ X81 @ X80) @ X82)
% 0.82/1.04            = (k1_setfam_1 @ (k2_tarski @ X80 @ (k10_relat_1 @ X81 @ X82))))
% 0.82/1.04          | ~ (v1_relat_1 @ X81))),
% 0.82/1.04      inference('demod', [status(thm)], ['107', '108'])).
% 0.82/1.04  thf('110', plain,
% 0.82/1.04      (((k10_relat_1 @ sk_A @ sk_C_2)
% 0.82/1.04         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C_2))),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('111', plain,
% 0.82/1.04      ((((k10_relat_1 @ sk_A @ sk_C_2)
% 0.82/1.04          != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_2))))
% 0.82/1.04        | ~ (v1_relat_1 @ sk_A))),
% 0.82/1.04      inference('sup-', [status(thm)], ['109', '110'])).
% 0.82/1.04  thf('112', plain, ((v1_relat_1 @ sk_A)),
% 0.82/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.04  thf('113', plain,
% 0.82/1.04      (((k10_relat_1 @ sk_A @ sk_C_2)
% 0.82/1.04         != (k1_setfam_1 @ (k2_tarski @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_2))))),
% 0.82/1.04      inference('demod', [status(thm)], ['111', '112'])).
% 0.82/1.04  thf('114', plain, ($false),
% 0.82/1.04      inference('simplify_reflect-', [status(thm)], ['106', '113'])).
% 0.82/1.04  
% 0.82/1.04  % SZS output end Refutation
% 0.82/1.04  
% 0.91/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
