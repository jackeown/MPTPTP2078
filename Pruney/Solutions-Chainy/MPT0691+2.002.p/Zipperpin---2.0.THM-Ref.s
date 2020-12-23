%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Sptk5DFwLb

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:17 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 204 expanded)
%              Number of leaves         :   37 (  76 expanded)
%              Depth                    :   24
%              Number of atoms          :  802 (1559 expanded)
%              Number of equality atoms :   71 ( 115 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X59 @ X58 ) @ X60 )
        = ( k3_xboole_0 @ X58 @ ( k10_relat_1 @ X59 @ X60 ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X59 @ X58 ) @ X60 )
        = ( k1_setfam_1 @ ( k2_tarski @ X58 @ ( k10_relat_1 @ X59 @ X60 ) ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) )
        = ( k9_relat_1 @ X50 @ X51 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X53 @ X54 ) @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k7_relat_1 @ X0 @ X1 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X45: $i,X47: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( r1_tarski @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) )
      | ( v1_relat_1 @ X48 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X52: $i] :
      ( ( ( k10_relat_1 @ X52 @ ( k2_relat_1 @ X52 ) )
        = ( k1_relat_1 @ X52 ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('23',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ X55 @ ( k1_relat_1 @ X56 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X56 @ X55 ) )
        = X55 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('27',plain,(
    ! [X57: $i] :
      ( ( ( k7_relat_1 @ X57 @ ( k1_relat_1 @ X57 ) )
        = X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('28',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k7_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X59 @ X58 ) @ X60 )
        = ( k1_setfam_1 @ ( k2_tarski @ X58 @ ( k10_relat_1 @ X59 @ X60 ) ) ) )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('40',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ! [X2: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X2 @ X2 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['18','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('54',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X2: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X2 @ X2 ) )
      = X2 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('59',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('60',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('61',plain,(
    ! [X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('64',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('67',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('68',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X11 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','71'])).

thf('73',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','72'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('75',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Sptk5DFwLb
% 0.17/0.37  % Computer   : n007.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 19:16:06 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 229 iterations in 0.084s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.38/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(t146_funct_1, conjecture,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.58         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i,B:$i]:
% 0.38/0.58        ( ( v1_relat_1 @ B ) =>
% 0.38/0.58          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.58            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t139_funct_1, axiom,
% 0.38/0.58    (![A:$i,B:$i,C:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ C ) =>
% 0.38/0.58       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.38/0.58         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.38/0.58         (((k10_relat_1 @ (k7_relat_1 @ X59 @ X58) @ X60)
% 0.38/0.58            = (k3_xboole_0 @ X58 @ (k10_relat_1 @ X59 @ X60)))
% 0.38/0.58          | ~ (v1_relat_1 @ X59))),
% 0.38/0.58      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.38/0.58  thf(t12_setfam_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X43 : $i, X44 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.38/0.58         (((k10_relat_1 @ (k7_relat_1 @ X59 @ X58) @ X60)
% 0.38/0.58            = (k1_setfam_1 @ (k2_tarski @ X58 @ (k10_relat_1 @ X59 @ X60))))
% 0.38/0.58          | ~ (v1_relat_1 @ X59))),
% 0.38/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf(t148_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      (![X50 : $i, X51 : $i]:
% 0.38/0.58         (((k2_relat_1 @ (k7_relat_1 @ X50 @ X51)) = (k9_relat_1 @ X50 @ X51))
% 0.38/0.58          | ~ (v1_relat_1 @ X50))),
% 0.38/0.58      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.38/0.58  thf(t88_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X53 : $i, X54 : $i]:
% 0.38/0.58         ((r1_tarski @ (k7_relat_1 @ X53 @ X54) @ X53) | ~ (v1_relat_1 @ X53))),
% 0.38/0.58      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.38/0.58  thf(t12_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X8 : $i, X9 : $i]:
% 0.38/0.58         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X0)
% 0.38/0.58          | ((k2_xboole_0 @ (k7_relat_1 @ X0 @ X1) @ X0) = (X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.58  thf(commutativity_k2_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X0)
% 0.38/0.58          | ((k2_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1)) = (X0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.38/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.38/0.58  thf(t7_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.38/0.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.58  thf(t3_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X45 : $i, X47 : $i]:
% 0.38/0.58         ((m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X47)) | ~ (r1_tarski @ X45 @ X47))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf(cc2_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X48 : $i, X49 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49))
% 0.38/0.58          | (v1_relat_1 @ X48)
% 0.38/0.58          | ~ (v1_relat_1 @ X49))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ (k2_xboole_0 @ X1 @ X0)) | (v1_relat_1 @ X1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ (k2_xboole_0 @ X1 @ X0)) | (v1_relat_1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['10', '15'])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '16'])).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.58  thf(t169_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (![X52 : $i]:
% 0.38/0.58         (((k10_relat_1 @ X52 @ (k2_relat_1 @ X52)) = (k1_relat_1 @ X52))
% 0.38/0.58          | ~ (v1_relat_1 @ X52))),
% 0.38/0.58      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.58  thf('22', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t91_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.58         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X55 : $i, X56 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X55 @ (k1_relat_1 @ X56))
% 0.38/0.58          | ((k1_relat_1 @ (k7_relat_1 @ X56 @ X55)) = (X55))
% 0.38/0.58          | ~ (v1_relat_1 @ X56))),
% 0.38/0.58      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.58        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.58  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('26', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.58  thf(t98_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X57 : $i]:
% 0.38/0.58         (((k7_relat_1 @ X57 @ (k1_relat_1 @ X57)) = (X57))
% 0.38/0.58          | ~ (v1_relat_1 @ X57))),
% 0.38/0.58      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      ((((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.58          = (k7_relat_1 @ sk_B @ sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['26', '27'])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.58        | ((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.58            = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['21', '28'])).
% 0.38/0.58  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (((k7_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.38/0.58         = (k7_relat_1 @ sk_B @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.38/0.58         (((k10_relat_1 @ (k7_relat_1 @ X59 @ X58) @ X60)
% 0.38/0.58            = (k1_setfam_1 @ (k2_tarski @ X58 @ (k10_relat_1 @ X59 @ X60))))
% 0.38/0.58          | ~ (v1_relat_1 @ X59))),
% 0.38/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)
% 0.38/0.58            = (k1_setfam_1 @ 
% 0.38/0.58               (k2_tarski @ sk_A @ 
% 0.38/0.58                (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))))
% 0.38/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['31', '32'])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ sk_B)
% 0.38/0.58          | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)
% 0.38/0.58              = (k1_setfam_1 @ 
% 0.38/0.58                 (k2_tarski @ sk_A @ 
% 0.38/0.58                  (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['20', '33'])).
% 0.38/0.58  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)
% 0.38/0.58           = (k1_setfam_1 @ 
% 0.38/0.58              (k2_tarski @ sk_A @ 
% 0.38/0.58               (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.38/0.58          (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.38/0.58          = (k1_setfam_1 @ 
% 0.38/0.58             (k2_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))
% 0.38/0.58        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['19', '36'])).
% 0.38/0.58  thf('38', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.38/0.58  thf(idempotence_k3_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.38/0.58  thf('39', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X43 : $i, X44 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      (![X2 : $i]: ((k1_setfam_1 @ (k2_tarski @ X2 @ X2)) = (X2))),
% 0.38/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.38/0.58          (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['37', '38', '41'])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      ((~ (v1_relat_1 @ sk_B)
% 0.38/0.58        | ((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.38/0.58            (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['18', '42'])).
% 0.38/0.58  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.38/0.58         (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))) = (sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['43', '44'])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      ((((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.38/0.58          = (sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.58      inference('sup+', [status(thm)], ['4', '45'])).
% 0.38/0.58  thf('47', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (((k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ (k9_relat_1 @ sk_B @ sk_A))
% 0.38/0.58         = (sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      ((((k1_setfam_1 @ 
% 0.38/0.58          (k2_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.38/0.58          = (sk_A))
% 0.38/0.58        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.58      inference('sup+', [status(thm)], ['3', '48'])).
% 0.38/0.58  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      (((k1_setfam_1 @ 
% 0.38/0.58         (k2_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.38/0.58         = (sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['49', '50'])).
% 0.38/0.58  thf(t100_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X6 @ X7)
% 0.38/0.58           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (![X43 : $i, X44 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X6 @ X7)
% 0.38/0.58           = (k5_xboole_0 @ X6 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 0.38/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.38/0.58         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.38/0.58      inference('sup+', [status(thm)], ['51', '54'])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (![X2 : $i]: ((k1_setfam_1 @ (k2_tarski @ X2 @ X2)) = (X2))),
% 0.38/0.58      inference('demod', [status(thm)], ['39', '40'])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X6 @ X7)
% 0.38/0.58           = (k5_xboole_0 @ X6 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 0.38/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['56', '57'])).
% 0.38/0.58  thf(t2_boole, axiom,
% 0.38/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.58  thf('59', plain,
% 0.38/0.58      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (![X43 : $i, X44 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.58  thf('61', plain,
% 0.38/0.58      (![X10 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X10 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X6 @ X7)
% 0.38/0.58           = (k5_xboole_0 @ X6 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 0.38/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.38/0.58  thf('63', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['61', '62'])).
% 0.38/0.58  thf(t5_boole, axiom,
% 0.38/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.58  thf('64', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.58  thf('65', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['63', '64'])).
% 0.38/0.58  thf(t48_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.58  thf('66', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.38/0.58           = (k3_xboole_0 @ X11 @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      (![X43 : $i, X44 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.38/0.58  thf('68', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.38/0.58           = (k1_setfam_1 @ (k2_tarski @ X11 @ X12)))),
% 0.38/0.58      inference('demod', [status(thm)], ['66', '67'])).
% 0.38/0.58  thf('69', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k4_xboole_0 @ X0 @ X0)
% 0.38/0.58           = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['65', '68'])).
% 0.38/0.58  thf('70', plain,
% 0.38/0.58      (![X10 : $i]:
% 0.38/0.58         ((k1_setfam_1 @ (k2_tarski @ X10 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.58  thf('71', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['69', '70'])).
% 0.38/0.58  thf('72', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['58', '71'])).
% 0.38/0.58  thf('73', plain,
% 0.38/0.58      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.38/0.58         = (k1_xboole_0))),
% 0.38/0.58      inference('demod', [status(thm)], ['55', '72'])).
% 0.38/0.58  thf(l32_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.58  thf('74', plain,
% 0.38/0.58      (![X3 : $i, X4 : $i]:
% 0.38/0.58         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.38/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.38/0.58  thf('75', plain,
% 0.38/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.58        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.58  thf('76', plain,
% 0.38/0.58      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['75'])).
% 0.38/0.58  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
