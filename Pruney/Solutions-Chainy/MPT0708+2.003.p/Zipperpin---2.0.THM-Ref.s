%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QjlSzSIQcI

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:04 EST 2020

% Result     : Theorem 4.08s
% Output     : Refutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 285 expanded)
%              Number of leaves         :   37 ( 103 expanded)
%              Depth                    :   27
%              Number of atoms          :  920 (2452 expanded)
%              Number of equality atoms :   63 ( 143 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t163_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t163_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X81 @ X80 ) @ X82 )
        = ( k3_xboole_0 @ X80 @ ( k10_relat_1 @ X81 @ X82 ) ) )
      | ~ ( v1_relat_1 @ X81 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X81 @ X80 ) @ X82 )
        = ( k1_setfam_1 @ ( k2_tarski @ X80 @ ( k10_relat_1 @ X81 @ X82 ) ) ) )
      | ~ ( v1_relat_1 @ X81 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ X56 @ X57 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X58 @ X57 ) @ X56 )
        = ( k9_relat_1 @ X58 @ X56 ) )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('11',plain,(
    ! [X76: $i,X77: $i] :
      ( ( ( k7_relat_1 @ X77 @ X76 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X76 ) @ X77 ) )
      | ~ ( v1_relat_1 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ( r1_tarski @ ( k2_xboole_0 @ X18 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A ) @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('21',plain,(
    ! [X73: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X73 ) )
      = X73 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X61: $i] :
      ( ( ( k10_relat_1 @ X61 @ ( k2_relat_1 @ X61 ) )
        = ( k1_relat_1 @ X61 ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X72: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X72 ) )
      = X72 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('27',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( ( k10_relat_1 @ X64 @ ( k2_xboole_0 @ X65 @ X66 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X64 @ X65 ) @ ( k10_relat_1 @ X64 @ X66 ) ) )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X72: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X72 ) )
      = X72 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X59 @ X60 ) @ ( k1_relat_1 @ X59 ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','35','36'])).

thf('38',plain,
    ( ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference('sup+',[status(thm)],['20','37'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('39',plain,(
    ! [X70: $i,X71: $i] :
      ( ~ ( v1_relat_1 @ X70 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X71 @ X70 ) )
        = ( k10_relat_1 @ X71 @ ( k1_relat_1 @ X70 ) ) )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('40',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X78: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['11','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X55: $i] :
      ( ( ( k9_relat_1 @ X55 @ ( k1_relat_1 @ X55 ) )
        = ( k2_relat_1 @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('48',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k9_relat_1 @ sk_C @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X61: $i] :
      ( ( ( k10_relat_1 @ X61 @ ( k2_relat_1 @ X61 ) )
        = ( k1_relat_1 @ X61 ) )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('56',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('58',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('63',plain,(
    ! [X67: $i,X68: $i,X69: $i] :
      ( ~ ( r1_tarski @ X67 @ X68 )
      | ~ ( v1_relat_1 @ X69 )
      | ( r1_tarski @ ( k10_relat_1 @ X69 @ X67 ) @ ( k10_relat_1 @ X69 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('70',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('71',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X59 @ X60 ) @ ( k1_relat_1 @ X59 ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','77'])).

thf('79',plain,
    ( ( sk_A
      = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['3','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('83',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('84',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('86',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('87',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) ) @ X10 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['81','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QjlSzSIQcI
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:01:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 4.08/4.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.08/4.28  % Solved by: fo/fo7.sh
% 4.08/4.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.08/4.28  % done 6921 iterations in 3.816s
% 4.08/4.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.08/4.28  % SZS output start Refutation
% 4.08/4.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.08/4.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.08/4.28  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 4.08/4.28  thf(sk_A_type, type, sk_A: $i).
% 4.08/4.28  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 4.08/4.28  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.08/4.28  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.08/4.28  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.08/4.28  thf(sk_C_type, type, sk_C: $i).
% 4.08/4.28  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 4.08/4.28  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.08/4.28  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.08/4.28  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.08/4.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.08/4.28  thf(sk_B_type, type, sk_B: $i).
% 4.08/4.28  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.08/4.28  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.08/4.28  thf(t163_funct_1, conjecture,
% 4.08/4.28    (![A:$i,B:$i,C:$i]:
% 4.08/4.28     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.08/4.28       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 4.08/4.28           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 4.08/4.28         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 4.08/4.28  thf(zf_stmt_0, negated_conjecture,
% 4.08/4.28    (~( ![A:$i,B:$i,C:$i]:
% 4.08/4.28        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 4.08/4.28          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 4.08/4.28              ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 4.08/4.28            ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 4.08/4.28    inference('cnf.neg', [status(esa)], [t163_funct_1])).
% 4.08/4.28  thf('0', plain, (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf(t139_funct_1, axiom,
% 4.08/4.28    (![A:$i,B:$i,C:$i]:
% 4.08/4.28     ( ( v1_relat_1 @ C ) =>
% 4.08/4.28       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 4.08/4.28         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 4.08/4.28  thf('1', plain,
% 4.08/4.28      (![X80 : $i, X81 : $i, X82 : $i]:
% 4.08/4.28         (((k10_relat_1 @ (k7_relat_1 @ X81 @ X80) @ X82)
% 4.08/4.28            = (k3_xboole_0 @ X80 @ (k10_relat_1 @ X81 @ X82)))
% 4.08/4.28          | ~ (v1_relat_1 @ X81))),
% 4.08/4.28      inference('cnf', [status(esa)], [t139_funct_1])).
% 4.08/4.28  thf(t12_setfam_1, axiom,
% 4.08/4.28    (![A:$i,B:$i]:
% 4.08/4.28     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.08/4.28  thf('2', plain,
% 4.08/4.28      (![X51 : $i, X52 : $i]:
% 4.08/4.28         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 4.08/4.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.08/4.28  thf('3', plain,
% 4.08/4.28      (![X80 : $i, X81 : $i, X82 : $i]:
% 4.08/4.28         (((k10_relat_1 @ (k7_relat_1 @ X81 @ X80) @ X82)
% 4.08/4.28            = (k1_setfam_1 @ (k2_tarski @ X80 @ (k10_relat_1 @ X81 @ X82))))
% 4.08/4.28          | ~ (v1_relat_1 @ X81))),
% 4.08/4.28      inference('demod', [status(thm)], ['1', '2'])).
% 4.08/4.28  thf(dt_k7_relat_1, axiom,
% 4.08/4.28    (![A:$i,B:$i]:
% 4.08/4.28     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 4.08/4.28  thf('4', plain,
% 4.08/4.28      (![X53 : $i, X54 : $i]:
% 4.08/4.28         (~ (v1_relat_1 @ X53) | (v1_relat_1 @ (k7_relat_1 @ X53 @ X54)))),
% 4.08/4.28      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 4.08/4.28  thf('5', plain,
% 4.08/4.28      (![X53 : $i, X54 : $i]:
% 4.08/4.28         (~ (v1_relat_1 @ X53) | (v1_relat_1 @ (k7_relat_1 @ X53 @ X54)))),
% 4.08/4.28      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 4.08/4.28  thf(d10_xboole_0, axiom,
% 4.08/4.28    (![A:$i,B:$i]:
% 4.08/4.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.08/4.28  thf('6', plain,
% 4.08/4.28      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 4.08/4.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.08/4.28  thf('7', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 4.08/4.28      inference('simplify', [status(thm)], ['6'])).
% 4.08/4.28  thf(t162_relat_1, axiom,
% 4.08/4.28    (![A:$i]:
% 4.08/4.28     ( ( v1_relat_1 @ A ) =>
% 4.08/4.28       ( ![B:$i,C:$i]:
% 4.08/4.28         ( ( r1_tarski @ B @ C ) =>
% 4.08/4.28           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 4.08/4.28             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 4.08/4.28  thf('8', plain,
% 4.08/4.28      (![X56 : $i, X57 : $i, X58 : $i]:
% 4.08/4.28         (~ (r1_tarski @ X56 @ X57)
% 4.08/4.28          | ((k9_relat_1 @ (k7_relat_1 @ X58 @ X57) @ X56)
% 4.08/4.28              = (k9_relat_1 @ X58 @ X56))
% 4.08/4.28          | ~ (v1_relat_1 @ X58))),
% 4.08/4.28      inference('cnf', [status(esa)], [t162_relat_1])).
% 4.08/4.28  thf('9', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]:
% 4.08/4.28         (~ (v1_relat_1 @ X1)
% 4.08/4.28          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 4.08/4.28              = (k9_relat_1 @ X1 @ X0)))),
% 4.08/4.28      inference('sup-', [status(thm)], ['7', '8'])).
% 4.08/4.28  thf('10', plain,
% 4.08/4.28      (![X53 : $i, X54 : $i]:
% 4.08/4.28         (~ (v1_relat_1 @ X53) | (v1_relat_1 @ (k7_relat_1 @ X53 @ X54)))),
% 4.08/4.28      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 4.08/4.28  thf(t94_relat_1, axiom,
% 4.08/4.28    (![A:$i,B:$i]:
% 4.08/4.28     ( ( v1_relat_1 @ B ) =>
% 4.08/4.28       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 4.08/4.28  thf('11', plain,
% 4.08/4.28      (![X76 : $i, X77 : $i]:
% 4.08/4.28         (((k7_relat_1 @ X77 @ X76) = (k5_relat_1 @ (k6_relat_1 @ X76) @ X77))
% 4.08/4.28          | ~ (v1_relat_1 @ X77))),
% 4.08/4.28      inference('cnf', [status(esa)], [t94_relat_1])).
% 4.08/4.28  thf('12', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf('13', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 4.08/4.28      inference('simplify', [status(thm)], ['6'])).
% 4.08/4.28  thf(t8_xboole_1, axiom,
% 4.08/4.28    (![A:$i,B:$i,C:$i]:
% 4.08/4.28     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 4.08/4.28       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.08/4.28  thf('14', plain,
% 4.08/4.28      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.08/4.28         (~ (r1_tarski @ X18 @ X19)
% 4.08/4.28          | ~ (r1_tarski @ X20 @ X19)
% 4.08/4.28          | (r1_tarski @ (k2_xboole_0 @ X18 @ X20) @ X19))),
% 4.08/4.28      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.08/4.28  thf('15', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]:
% 4.08/4.28         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 4.08/4.28      inference('sup-', [status(thm)], ['13', '14'])).
% 4.08/4.28  thf('16', plain,
% 4.08/4.28      ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) @ 
% 4.08/4.28        (k1_relat_1 @ sk_C))),
% 4.08/4.28      inference('sup-', [status(thm)], ['12', '15'])).
% 4.08/4.28  thf(t7_xboole_1, axiom,
% 4.08/4.28    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.08/4.28  thf('17', plain,
% 4.08/4.28      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 4.08/4.28      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.08/4.28  thf('18', plain,
% 4.08/4.28      (![X2 : $i, X4 : $i]:
% 4.08/4.28         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 4.08/4.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.08/4.28  thf('19', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]:
% 4.08/4.28         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 4.08/4.28          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 4.08/4.28      inference('sup-', [status(thm)], ['17', '18'])).
% 4.08/4.28  thf('20', plain,
% 4.08/4.28      (((k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))),
% 4.08/4.28      inference('sup-', [status(thm)], ['16', '19'])).
% 4.08/4.28  thf(t71_relat_1, axiom,
% 4.08/4.28    (![A:$i]:
% 4.08/4.28     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 4.08/4.28       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 4.08/4.28  thf('21', plain, (![X73 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X73)) = (X73))),
% 4.08/4.28      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.08/4.28  thf(t169_relat_1, axiom,
% 4.08/4.28    (![A:$i]:
% 4.08/4.28     ( ( v1_relat_1 @ A ) =>
% 4.08/4.28       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 4.08/4.28  thf('22', plain,
% 4.08/4.28      (![X61 : $i]:
% 4.08/4.28         (((k10_relat_1 @ X61 @ (k2_relat_1 @ X61)) = (k1_relat_1 @ X61))
% 4.08/4.28          | ~ (v1_relat_1 @ X61))),
% 4.08/4.28      inference('cnf', [status(esa)], [t169_relat_1])).
% 4.08/4.28  thf('23', plain,
% 4.08/4.28      (![X0 : $i]:
% 4.08/4.28         (((k10_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 4.08/4.28            = (k1_relat_1 @ (k6_relat_1 @ X0)))
% 4.08/4.28          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.08/4.28      inference('sup+', [status(thm)], ['21', '22'])).
% 4.08/4.28  thf('24', plain, (![X72 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X72)) = (X72))),
% 4.08/4.28      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.08/4.28  thf(fc3_funct_1, axiom,
% 4.08/4.28    (![A:$i]:
% 4.08/4.28     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.08/4.28       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.08/4.28  thf('25', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 4.08/4.28      inference('cnf', [status(esa)], [fc3_funct_1])).
% 4.08/4.28  thf('26', plain,
% 4.08/4.28      (![X0 : $i]: ((k10_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 4.08/4.28      inference('demod', [status(thm)], ['23', '24', '25'])).
% 4.08/4.28  thf(t175_relat_1, axiom,
% 4.08/4.28    (![A:$i,B:$i,C:$i]:
% 4.08/4.28     ( ( v1_relat_1 @ C ) =>
% 4.08/4.28       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 4.08/4.28         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 4.08/4.28  thf('27', plain,
% 4.08/4.28      (![X64 : $i, X65 : $i, X66 : $i]:
% 4.08/4.28         (((k10_relat_1 @ X64 @ (k2_xboole_0 @ X65 @ X66))
% 4.08/4.28            = (k2_xboole_0 @ (k10_relat_1 @ X64 @ X65) @ 
% 4.08/4.28               (k10_relat_1 @ X64 @ X66)))
% 4.08/4.28          | ~ (v1_relat_1 @ X64))),
% 4.08/4.28      inference('cnf', [status(esa)], [t175_relat_1])).
% 4.08/4.28  thf('28', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]:
% 4.08/4.28         (((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 4.08/4.28            = (k2_xboole_0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0))
% 4.08/4.28          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.08/4.28      inference('sup+', [status(thm)], ['26', '27'])).
% 4.08/4.28  thf('29', plain, (![X72 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X72)) = (X72))),
% 4.08/4.28      inference('cnf', [status(esa)], [t71_relat_1])).
% 4.08/4.28  thf(t167_relat_1, axiom,
% 4.08/4.28    (![A:$i,B:$i]:
% 4.08/4.28     ( ( v1_relat_1 @ B ) =>
% 4.08/4.28       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 4.08/4.28  thf('30', plain,
% 4.08/4.28      (![X59 : $i, X60 : $i]:
% 4.08/4.28         ((r1_tarski @ (k10_relat_1 @ X59 @ X60) @ (k1_relat_1 @ X59))
% 4.08/4.28          | ~ (v1_relat_1 @ X59))),
% 4.08/4.28      inference('cnf', [status(esa)], [t167_relat_1])).
% 4.08/4.28  thf('31', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]:
% 4.08/4.28         ((r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)
% 4.08/4.28          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 4.08/4.28      inference('sup+', [status(thm)], ['29', '30'])).
% 4.08/4.28  thf('32', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 4.08/4.28      inference('cnf', [status(esa)], [fc3_funct_1])).
% 4.08/4.28  thf('33', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]:
% 4.08/4.28         (r1_tarski @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0)),
% 4.08/4.28      inference('demod', [status(thm)], ['31', '32'])).
% 4.08/4.28  thf(t12_xboole_1, axiom,
% 4.08/4.28    (![A:$i,B:$i]:
% 4.08/4.28     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 4.08/4.28  thf('34', plain,
% 4.08/4.28      (![X8 : $i, X9 : $i]:
% 4.08/4.28         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 4.08/4.28      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.08/4.28  thf('35', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]:
% 4.08/4.28         ((k2_xboole_0 @ (k10_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X0) = (X0))),
% 4.08/4.28      inference('sup-', [status(thm)], ['33', '34'])).
% 4.08/4.28  thf('36', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 4.08/4.28      inference('cnf', [status(esa)], [fc3_funct_1])).
% 4.08/4.28  thf('37', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]:
% 4.08/4.28         ((k10_relat_1 @ (k6_relat_1 @ X0) @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 4.08/4.28      inference('demod', [status(thm)], ['28', '35', '36'])).
% 4.08/4.28  thf('38', plain,
% 4.08/4.28      (((k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 4.08/4.28      inference('sup+', [status(thm)], ['20', '37'])).
% 4.08/4.28  thf(t182_relat_1, axiom,
% 4.08/4.28    (![A:$i]:
% 4.08/4.28     ( ( v1_relat_1 @ A ) =>
% 4.08/4.28       ( ![B:$i]:
% 4.08/4.28         ( ( v1_relat_1 @ B ) =>
% 4.08/4.28           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 4.08/4.28             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 4.08/4.28  thf('39', plain,
% 4.08/4.28      (![X70 : $i, X71 : $i]:
% 4.08/4.28         (~ (v1_relat_1 @ X70)
% 4.08/4.28          | ((k1_relat_1 @ (k5_relat_1 @ X71 @ X70))
% 4.08/4.28              = (k10_relat_1 @ X71 @ (k1_relat_1 @ X70)))
% 4.08/4.28          | ~ (v1_relat_1 @ X71))),
% 4.08/4.28      inference('cnf', [status(esa)], [t182_relat_1])).
% 4.08/4.28  thf('40', plain,
% 4.08/4.28      ((((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)) = (sk_A))
% 4.08/4.28        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 4.08/4.28        | ~ (v1_relat_1 @ sk_C))),
% 4.08/4.28      inference('sup+', [status(thm)], ['38', '39'])).
% 4.08/4.28  thf('41', plain, (![X78 : $i]: (v1_relat_1 @ (k6_relat_1 @ X78))),
% 4.08/4.28      inference('cnf', [status(esa)], [fc3_funct_1])).
% 4.08/4.28  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf('43', plain,
% 4.08/4.28      (((k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C)) = (sk_A))),
% 4.08/4.28      inference('demod', [status(thm)], ['40', '41', '42'])).
% 4.08/4.28  thf('44', plain,
% 4.08/4.28      ((((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) = (sk_A))
% 4.08/4.28        | ~ (v1_relat_1 @ sk_C))),
% 4.08/4.28      inference('sup+', [status(thm)], ['11', '43'])).
% 4.08/4.28  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf('46', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 4.08/4.28      inference('demod', [status(thm)], ['44', '45'])).
% 4.08/4.28  thf(t146_relat_1, axiom,
% 4.08/4.28    (![A:$i]:
% 4.08/4.28     ( ( v1_relat_1 @ A ) =>
% 4.08/4.28       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 4.08/4.28  thf('47', plain,
% 4.08/4.28      (![X55 : $i]:
% 4.08/4.28         (((k9_relat_1 @ X55 @ (k1_relat_1 @ X55)) = (k2_relat_1 @ X55))
% 4.08/4.28          | ~ (v1_relat_1 @ X55))),
% 4.08/4.28      inference('cnf', [status(esa)], [t146_relat_1])).
% 4.08/4.28  thf('48', plain,
% 4.08/4.28      ((((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_A)
% 4.08/4.28          = (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 4.08/4.28        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 4.08/4.28      inference('sup+', [status(thm)], ['46', '47'])).
% 4.08/4.28  thf('49', plain,
% 4.08/4.28      ((~ (v1_relat_1 @ sk_C)
% 4.08/4.28        | ((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_A)
% 4.08/4.28            = (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))))),
% 4.08/4.28      inference('sup-', [status(thm)], ['10', '48'])).
% 4.08/4.28  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf('51', plain,
% 4.08/4.28      (((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_A)
% 4.08/4.28         = (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 4.08/4.28      inference('demod', [status(thm)], ['49', '50'])).
% 4.08/4.28  thf('52', plain,
% 4.08/4.28      ((((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 4.08/4.28        | ~ (v1_relat_1 @ sk_C))),
% 4.08/4.28      inference('sup+', [status(thm)], ['9', '51'])).
% 4.08/4.28  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf('54', plain,
% 4.08/4.28      (((k9_relat_1 @ sk_C @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 4.08/4.28      inference('demod', [status(thm)], ['52', '53'])).
% 4.08/4.28  thf('55', plain,
% 4.08/4.28      (![X61 : $i]:
% 4.08/4.28         (((k10_relat_1 @ X61 @ (k2_relat_1 @ X61)) = (k1_relat_1 @ X61))
% 4.08/4.28          | ~ (v1_relat_1 @ X61))),
% 4.08/4.28      inference('cnf', [status(esa)], [t169_relat_1])).
% 4.08/4.28  thf('56', plain,
% 4.08/4.28      ((((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_A))
% 4.08/4.28          = (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))
% 4.08/4.28        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 4.08/4.28      inference('sup+', [status(thm)], ['54', '55'])).
% 4.08/4.28  thf('57', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 4.08/4.28      inference('demod', [status(thm)], ['44', '45'])).
% 4.08/4.28  thf('58', plain,
% 4.08/4.28      ((((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_A))
% 4.08/4.28          = (sk_A))
% 4.08/4.28        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 4.08/4.28      inference('demod', [status(thm)], ['56', '57'])).
% 4.08/4.28  thf('59', plain,
% 4.08/4.28      ((~ (v1_relat_1 @ sk_C)
% 4.08/4.28        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 4.08/4.28            (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 4.08/4.28      inference('sup-', [status(thm)], ['5', '58'])).
% 4.08/4.28  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf('61', plain,
% 4.08/4.28      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_A))
% 4.08/4.28         = (sk_A))),
% 4.08/4.28      inference('demod', [status(thm)], ['59', '60'])).
% 4.08/4.28  thf('62', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf(t178_relat_1, axiom,
% 4.08/4.28    (![A:$i,B:$i,C:$i]:
% 4.08/4.28     ( ( v1_relat_1 @ C ) =>
% 4.08/4.28       ( ( r1_tarski @ A @ B ) =>
% 4.08/4.28         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 4.08/4.28  thf('63', plain,
% 4.08/4.28      (![X67 : $i, X68 : $i, X69 : $i]:
% 4.08/4.28         (~ (r1_tarski @ X67 @ X68)
% 4.08/4.28          | ~ (v1_relat_1 @ X69)
% 4.08/4.28          | (r1_tarski @ (k10_relat_1 @ X69 @ X67) @ (k10_relat_1 @ X69 @ X68)))),
% 4.08/4.28      inference('cnf', [status(esa)], [t178_relat_1])).
% 4.08/4.28  thf('64', plain,
% 4.08/4.28      (![X0 : $i]:
% 4.08/4.28         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 4.08/4.28           (k10_relat_1 @ X0 @ sk_B))
% 4.08/4.28          | ~ (v1_relat_1 @ X0))),
% 4.08/4.28      inference('sup-', [status(thm)], ['62', '63'])).
% 4.08/4.28  thf('65', plain,
% 4.08/4.28      (((r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))
% 4.08/4.28        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 4.08/4.28      inference('sup+', [status(thm)], ['61', '64'])).
% 4.08/4.28  thf('66', plain,
% 4.08/4.28      ((~ (v1_relat_1 @ sk_C)
% 4.08/4.28        | (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)))),
% 4.08/4.28      inference('sup-', [status(thm)], ['4', '65'])).
% 4.08/4.28  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf('68', plain,
% 4.08/4.28      ((r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 4.08/4.28      inference('demod', [status(thm)], ['66', '67'])).
% 4.08/4.28  thf('69', plain,
% 4.08/4.28      (![X53 : $i, X54 : $i]:
% 4.08/4.28         (~ (v1_relat_1 @ X53) | (v1_relat_1 @ (k7_relat_1 @ X53 @ X54)))),
% 4.08/4.28      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 4.08/4.28  thf('70', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 4.08/4.28      inference('demod', [status(thm)], ['44', '45'])).
% 4.08/4.28  thf('71', plain,
% 4.08/4.28      (![X59 : $i, X60 : $i]:
% 4.08/4.28         ((r1_tarski @ (k10_relat_1 @ X59 @ X60) @ (k1_relat_1 @ X59))
% 4.08/4.28          | ~ (v1_relat_1 @ X59))),
% 4.08/4.28      inference('cnf', [status(esa)], [t167_relat_1])).
% 4.08/4.28  thf('72', plain,
% 4.08/4.28      (![X0 : $i]:
% 4.08/4.28         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ X0) @ sk_A)
% 4.08/4.28          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 4.08/4.28      inference('sup+', [status(thm)], ['70', '71'])).
% 4.08/4.28  thf('73', plain,
% 4.08/4.28      (![X0 : $i]:
% 4.08/4.28         (~ (v1_relat_1 @ sk_C)
% 4.08/4.28          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ X0) @ sk_A))),
% 4.08/4.28      inference('sup-', [status(thm)], ['69', '72'])).
% 4.08/4.28  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf('75', plain,
% 4.08/4.28      (![X0 : $i]:
% 4.08/4.28         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ X0) @ sk_A)),
% 4.08/4.28      inference('demod', [status(thm)], ['73', '74'])).
% 4.08/4.28  thf('76', plain,
% 4.08/4.28      (![X2 : $i, X4 : $i]:
% 4.08/4.28         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 4.08/4.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.08/4.28  thf('77', plain,
% 4.08/4.28      (![X0 : $i]:
% 4.08/4.28         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ X0))
% 4.08/4.28          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ X0)))),
% 4.08/4.28      inference('sup-', [status(thm)], ['75', '76'])).
% 4.08/4.28  thf('78', plain,
% 4.08/4.28      (((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 4.08/4.28      inference('sup-', [status(thm)], ['68', '77'])).
% 4.08/4.28  thf('79', plain,
% 4.08/4.28      ((((sk_A)
% 4.08/4.28          = (k1_setfam_1 @ (k2_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))))
% 4.08/4.28        | ~ (v1_relat_1 @ sk_C))),
% 4.08/4.28      inference('sup+', [status(thm)], ['3', '78'])).
% 4.08/4.28  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 4.08/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.08/4.28  thf('81', plain,
% 4.08/4.28      (((sk_A)
% 4.08/4.28         = (k1_setfam_1 @ (k2_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))))),
% 4.08/4.28      inference('demod', [status(thm)], ['79', '80'])).
% 4.08/4.28  thf(commutativity_k3_xboole_0, axiom,
% 4.08/4.28    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.08/4.28  thf('82', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.08/4.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.08/4.28  thf('83', plain,
% 4.08/4.28      (![X51 : $i, X52 : $i]:
% 4.08/4.28         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 4.08/4.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.08/4.28  thf('84', plain,
% 4.08/4.28      (![X51 : $i, X52 : $i]:
% 4.08/4.28         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 4.08/4.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.08/4.28  thf('85', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]:
% 4.08/4.28         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 4.08/4.28           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 4.08/4.28      inference('demod', [status(thm)], ['82', '83', '84'])).
% 4.08/4.28  thf(t17_xboole_1, axiom,
% 4.08/4.28    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 4.08/4.28  thf('86', plain,
% 4.08/4.28      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 4.08/4.28      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.08/4.28  thf('87', plain,
% 4.08/4.28      (![X51 : $i, X52 : $i]:
% 4.08/4.28         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 4.08/4.28      inference('cnf', [status(esa)], [t12_setfam_1])).
% 4.08/4.28  thf('88', plain,
% 4.08/4.28      (![X10 : $i, X11 : $i]:
% 4.08/4.28         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X10 @ X11)) @ X10)),
% 4.08/4.28      inference('demod', [status(thm)], ['86', '87'])).
% 4.08/4.28  thf('89', plain,
% 4.08/4.28      (![X0 : $i, X1 : $i]:
% 4.08/4.28         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 4.08/4.28      inference('sup+', [status(thm)], ['85', '88'])).
% 4.08/4.28  thf('90', plain, ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))),
% 4.08/4.28      inference('sup+', [status(thm)], ['81', '89'])).
% 4.08/4.28  thf('91', plain, ($false), inference('demod', [status(thm)], ['0', '90'])).
% 4.08/4.28  
% 4.08/4.28  % SZS output end Refutation
% 4.08/4.28  
% 4.08/4.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
