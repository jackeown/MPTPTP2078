%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Geew89T4sE

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:25 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 175 expanded)
%              Number of leaves         :   33 (  67 expanded)
%              Depth                    :   26
%              Number of atoms          :  721 (1427 expanded)
%              Number of equality atoms :   63 ( 105 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X60 @ X59 ) @ X61 )
        = ( k3_xboole_0 @ X59 @ ( k10_relat_1 @ X60 @ X61 ) ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X60 @ X59 ) @ X61 )
        = ( k1_setfam_1 @ ( k2_tarski @ X59 @ ( k10_relat_1 @ X60 @ X61 ) ) ) )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ X46 @ X47 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X48 @ X47 ) @ X46 )
        = ( k9_relat_1 @ X48 @ X46 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('10',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k7_relat_1 @ X56 @ X55 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X55 ) @ X56 ) )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X50 @ X49 ) )
        = ( k10_relat_1 @ X50 @ ( k1_relat_1 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('13',plain,(
    ! [X52: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X52 ) )
      = X52 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('14',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X53 ) @ X54 )
      | ( ( k5_relat_1 @ X53 @ ( k6_relat_1 @ X54 ) )
        = X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X57: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X51: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X51 ) )
      = X51 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('20',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X50 @ X49 ) )
        = ( k10_relat_1 @ X50 @ ( k1_relat_1 @ X49 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X57: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X51: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X51 ) )
      = X51 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('26',plain,(
    ! [X57: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','27'])).

thf('29',plain,(
    ! [X57: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( sk_A
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['10','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X43: $i] :
      ( ( ( k9_relat_1 @ X43 @ ( k1_relat_1 @ X43 ) )
        = ( k2_relat_1 @ X43 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('36',plain,
    ( ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('44',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X53 ) @ X54 )
      | ( ( k5_relat_1 @ X53 @ ( k6_relat_1 @ X54 ) )
        = X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,
    ( sk_A
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('51',plain,
    ( ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( sk_A
    = ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('62',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Geew89T4sE
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:49:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 409 iterations in 0.258s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.47/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.70  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.47/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.70  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(t146_funct_1, conjecture,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ B ) =>
% 0.47/0.70       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.70         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i,B:$i]:
% 0.47/0.70        ( ( v1_relat_1 @ B ) =>
% 0.47/0.70          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.70            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.47/0.70  thf('0', plain,
% 0.47/0.70      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(t139_funct_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ C ) =>
% 0.47/0.70       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.47/0.70         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.47/0.70         (((k10_relat_1 @ (k7_relat_1 @ X60 @ X59) @ X61)
% 0.47/0.70            = (k3_xboole_0 @ X59 @ (k10_relat_1 @ X60 @ X61)))
% 0.47/0.70          | ~ (v1_relat_1 @ X60))),
% 0.47/0.70      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.47/0.70  thf(t12_setfam_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.70  thf('2', plain,
% 0.47/0.70      (![X39 : $i, X40 : $i]:
% 0.47/0.70         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.47/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.70  thf('3', plain,
% 0.47/0.70      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.47/0.70         (((k10_relat_1 @ (k7_relat_1 @ X60 @ X59) @ X61)
% 0.47/0.70            = (k1_setfam_1 @ (k2_tarski @ X59 @ (k10_relat_1 @ X60 @ X61))))
% 0.47/0.70          | ~ (v1_relat_1 @ X60))),
% 0.47/0.70      inference('demod', [status(thm)], ['1', '2'])).
% 0.47/0.70  thf(dt_k7_relat_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.47/0.70  thf('4', plain,
% 0.47/0.70      (![X41 : $i, X42 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X41) | (v1_relat_1 @ (k7_relat_1 @ X41 @ X42)))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.47/0.70  thf(d10_xboole_0, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.70  thf('5', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.70  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.70  thf(t162_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ![B:$i,C:$i]:
% 0.47/0.70         ( ( r1_tarski @ B @ C ) =>
% 0.47/0.70           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.47/0.70             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.47/0.70  thf('7', plain,
% 0.47/0.70      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X46 @ X47)
% 0.47/0.70          | ((k9_relat_1 @ (k7_relat_1 @ X48 @ X47) @ X46)
% 0.47/0.70              = (k9_relat_1 @ X48 @ X46))
% 0.47/0.70          | ~ (v1_relat_1 @ X48))),
% 0.47/0.70      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X1)
% 0.47/0.70          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)
% 0.47/0.70              = (k9_relat_1 @ X1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.70  thf('9', plain,
% 0.47/0.70      (![X41 : $i, X42 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X41) | (v1_relat_1 @ (k7_relat_1 @ X41 @ X42)))),
% 0.47/0.70      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.47/0.70  thf(t94_relat_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ B ) =>
% 0.47/0.70       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.47/0.70  thf('10', plain,
% 0.47/0.70      (![X55 : $i, X56 : $i]:
% 0.47/0.70         (((k7_relat_1 @ X56 @ X55) = (k5_relat_1 @ (k6_relat_1 @ X55) @ X56))
% 0.47/0.70          | ~ (v1_relat_1 @ X56))),
% 0.47/0.70      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.47/0.70  thf(t182_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( v1_relat_1 @ B ) =>
% 0.47/0.70           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.47/0.70             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      (![X49 : $i, X50 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X49)
% 0.47/0.70          | ((k1_relat_1 @ (k5_relat_1 @ X50 @ X49))
% 0.47/0.70              = (k10_relat_1 @ X50 @ (k1_relat_1 @ X49)))
% 0.47/0.70          | ~ (v1_relat_1 @ X50))),
% 0.47/0.70      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.47/0.70  thf('12', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(t71_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.47/0.70       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.47/0.70  thf('13', plain, (![X52 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X52)) = (X52))),
% 0.47/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.70  thf(t79_relat_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ B ) =>
% 0.47/0.70       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.47/0.70         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.47/0.70  thf('14', plain,
% 0.47/0.70      (![X53 : $i, X54 : $i]:
% 0.47/0.70         (~ (r1_tarski @ (k2_relat_1 @ X53) @ X54)
% 0.47/0.70          | ((k5_relat_1 @ X53 @ (k6_relat_1 @ X54)) = (X53))
% 0.47/0.70          | ~ (v1_relat_1 @ X53))),
% 0.47/0.70      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.47/0.70  thf('15', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X0 @ X1)
% 0.47/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.47/0.70          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.47/0.70              = (k6_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.70  thf(fc3_funct_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.70       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.70  thf('16', plain, (![X57 : $i]: (v1_relat_1 @ (k6_relat_1 @ X57))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.70  thf('17', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (r1_tarski @ X0 @ X1)
% 0.47/0.70          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.47/0.70              = (k6_relat_1 @ X0)))),
% 0.47/0.70      inference('demod', [status(thm)], ['15', '16'])).
% 0.47/0.70  thf('18', plain,
% 0.47/0.70      (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 0.47/0.70         = (k6_relat_1 @ sk_A))),
% 0.47/0.70      inference('sup-', [status(thm)], ['12', '17'])).
% 0.47/0.70  thf('19', plain, (![X51 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X51)) = (X51))),
% 0.47/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.70  thf('20', plain,
% 0.47/0.70      (![X49 : $i, X50 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X49)
% 0.47/0.70          | ((k1_relat_1 @ (k5_relat_1 @ X50 @ X49))
% 0.47/0.70              = (k10_relat_1 @ X50 @ (k1_relat_1 @ X49)))
% 0.47/0.70          | ~ (v1_relat_1 @ X50))),
% 0.47/0.70      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.47/0.70  thf('21', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.47/0.70            = (k10_relat_1 @ X1 @ X0))
% 0.47/0.70          | ~ (v1_relat_1 @ X1)
% 0.47/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.47/0.70      inference('sup+', [status(thm)], ['19', '20'])).
% 0.47/0.70  thf('22', plain, (![X57 : $i]: (v1_relat_1 @ (k6_relat_1 @ X57))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.70  thf('23', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.47/0.70            = (k10_relat_1 @ X1 @ X0))
% 0.47/0.70          | ~ (v1_relat_1 @ X1))),
% 0.47/0.70      inference('demod', [status(thm)], ['21', '22'])).
% 0.47/0.70  thf('24', plain,
% 0.47/0.70      ((((k1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.47/0.70          = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.47/0.70        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.47/0.70      inference('sup+', [status(thm)], ['18', '23'])).
% 0.47/0.70  thf('25', plain, (![X51 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X51)) = (X51))),
% 0.47/0.70      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.70  thf('26', plain, (![X57 : $i]: (v1_relat_1 @ (k6_relat_1 @ X57))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.70  thf('27', plain,
% 0.47/0.70      (((sk_A) = (k10_relat_1 @ (k6_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 0.47/0.70      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.47/0.70  thf('28', plain,
% 0.47/0.70      ((((sk_A) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))
% 0.47/0.70        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.47/0.70        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.70      inference('sup+', [status(thm)], ['11', '27'])).
% 0.47/0.70  thf('29', plain, (![X57 : $i]: (v1_relat_1 @ (k6_relat_1 @ X57))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.47/0.70  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('31', plain,
% 0.47/0.70      (((sk_A) = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.47/0.70      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.47/0.70  thf('32', plain,
% 0.47/0.70      ((((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.47/0.70        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.70      inference('sup+', [status(thm)], ['10', '31'])).
% 0.47/0.70  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('34', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.70      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.70  thf(t146_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.47/0.70  thf('35', plain,
% 0.47/0.70      (![X43 : $i]:
% 0.47/0.70         (((k9_relat_1 @ X43 @ (k1_relat_1 @ X43)) = (k2_relat_1 @ X43))
% 0.47/0.70          | ~ (v1_relat_1 @ X43))),
% 0.47/0.70      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.47/0.70  thf('36', plain,
% 0.47/0.70      ((((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.47/0.70          = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.47/0.70        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.70      inference('sup+', [status(thm)], ['34', '35'])).
% 0.47/0.70  thf('37', plain,
% 0.47/0.70      ((~ (v1_relat_1 @ sk_B)
% 0.47/0.70        | ((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.47/0.71            = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['9', '36'])).
% 0.47/0.71  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('39', plain,
% 0.47/0.71      (((k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ sk_A)
% 0.47/0.71         = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.71      inference('demod', [status(thm)], ['37', '38'])).
% 0.47/0.71  thf('40', plain,
% 0.47/0.71      ((((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.47/0.71        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['8', '39'])).
% 0.47/0.71  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('42', plain,
% 0.47/0.71      (((k9_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.71      inference('demod', [status(thm)], ['40', '41'])).
% 0.47/0.71  thf('43', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.71      inference('simplify', [status(thm)], ['5'])).
% 0.47/0.71  thf('44', plain,
% 0.47/0.71      (![X53 : $i, X54 : $i]:
% 0.47/0.71         (~ (r1_tarski @ (k2_relat_1 @ X53) @ X54)
% 0.47/0.71          | ((k5_relat_1 @ X53 @ (k6_relat_1 @ X54)) = (X53))
% 0.47/0.71          | ~ (v1_relat_1 @ X53))),
% 0.47/0.71      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.47/0.71  thf('45', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X0)
% 0.47/0.71          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.71  thf('46', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.47/0.71            = (k10_relat_1 @ X1 @ X0))
% 0.47/0.71          | ~ (v1_relat_1 @ X1))),
% 0.47/0.71      inference('demod', [status(thm)], ['21', '22'])).
% 0.47/0.71  thf('47', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['45', '46'])).
% 0.47/0.71  thf('48', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X0)
% 0.47/0.71          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 0.47/0.71      inference('simplify', [status(thm)], ['47'])).
% 0.47/0.71  thf('49', plain,
% 0.47/0.71      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.47/0.71          = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.47/0.71             (k9_relat_1 @ sk_B @ sk_A)))
% 0.47/0.71        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['42', '48'])).
% 0.47/0.71  thf('50', plain, (((sk_A) = (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.71      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.71  thf('51', plain,
% 0.47/0.71      ((((sk_A)
% 0.47/0.71          = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.47/0.71             (k9_relat_1 @ sk_B @ sk_A)))
% 0.47/0.71        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.71      inference('demod', [status(thm)], ['49', '50'])).
% 0.47/0.71  thf('52', plain,
% 0.47/0.71      ((~ (v1_relat_1 @ sk_B)
% 0.47/0.71        | ((sk_A)
% 0.47/0.71            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.47/0.71               (k9_relat_1 @ sk_B @ sk_A))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['4', '51'])).
% 0.47/0.71  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('54', plain,
% 0.47/0.71      (((sk_A)
% 0.47/0.71         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.47/0.71            (k9_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.71      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.71  thf('55', plain,
% 0.47/0.71      ((((sk_A)
% 0.47/0.71          = (k1_setfam_1 @ 
% 0.47/0.71             (k2_tarski @ sk_A @ 
% 0.47/0.71              (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))
% 0.47/0.71        | ~ (v1_relat_1 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['3', '54'])).
% 0.47/0.71  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('57', plain,
% 0.47/0.71      (((sk_A)
% 0.47/0.71         = (k1_setfam_1 @ 
% 0.47/0.71            (k2_tarski @ sk_A @ 
% 0.47/0.71             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))))),
% 0.47/0.71      inference('demod', [status(thm)], ['55', '56'])).
% 0.47/0.71  thf(t100_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.71  thf('58', plain,
% 0.47/0.71      (![X6 : $i, X7 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X6 @ X7)
% 0.47/0.71           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.47/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.71  thf('59', plain,
% 0.47/0.71      (![X39 : $i, X40 : $i]:
% 0.47/0.71         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.47/0.71      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.47/0.71  thf('60', plain,
% 0.47/0.71      (![X6 : $i, X7 : $i]:
% 0.47/0.71         ((k4_xboole_0 @ X6 @ X7)
% 0.47/0.71           = (k5_xboole_0 @ X6 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 0.47/0.71      inference('demod', [status(thm)], ['58', '59'])).
% 0.47/0.71  thf('61', plain,
% 0.47/0.71      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.47/0.71         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.47/0.71      inference('sup+', [status(thm)], ['57', '60'])).
% 0.47/0.71  thf(t92_xboole_1, axiom,
% 0.47/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.47/0.71  thf('62', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 0.47/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.47/0.71  thf('63', plain,
% 0.47/0.71      (((k4_xboole_0 @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))
% 0.47/0.71         = (k1_xboole_0))),
% 0.47/0.71      inference('demod', [status(thm)], ['61', '62'])).
% 0.47/0.71  thf(l32_xboole_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.71  thf('64', plain,
% 0.47/0.71      (![X3 : $i, X4 : $i]:
% 0.47/0.71         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.47/0.71      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.47/0.71  thf('65', plain,
% 0.47/0.71      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.71        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['63', '64'])).
% 0.47/0.71  thf('66', plain,
% 0.47/0.71      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.47/0.71      inference('simplify', [status(thm)], ['65'])).
% 0.47/0.71  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 0.47/0.71  
% 0.47/0.71  % SZS output end Refutation
% 0.47/0.71  
% 0.54/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
