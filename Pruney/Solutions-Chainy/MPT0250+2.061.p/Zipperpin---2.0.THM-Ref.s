%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WuS1gpe1pj

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:55 EST 2020

% Result     : Theorem 2.90s
% Output     : Refutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 434 expanded)
%              Number of leaves         :   31 ( 158 expanded)
%              Depth                    :   18
%              Number of atoms          :  798 (4294 expanded)
%              Number of equality atoms :   54 ( 282 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('6',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 )
      = ( k2_enumset1 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('7',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X20 @ X19 @ X18 @ X17 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X49 )
      = ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X49 )
      = ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('16',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i,X72: $i,X73: $i,X74: $i] :
      ( ( k6_enumset1 @ X68 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 )
      = ( k5_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X9 @ X10 @ X11 @ X12 ) @ ( k2_enumset1 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X6 @ X6 @ X5 @ X4 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( r1_tarski @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k5_enumset1 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('24',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i,X66: $i,X67: $i] :
      ( ( k5_enumset1 @ X62 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 )
      = ( k4_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('25',plain,(
    ! [X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k4_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61 )
      = ( k3_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','26'])).

thf('28',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X77: $i,X78: $i,X79: $i] :
      ( ( r2_hidden @ X77 @ X78 )
      | ~ ( r1_tarski @ ( k2_tarski @ X77 @ X79 ) @ X78 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56 )
      = ( k2_enumset1 @ X53 @ X54 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('33',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X49 )
      = ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X77: $i,X79: $i,X80: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X77 @ X79 ) @ X80 )
      | ~ ( r2_hidden @ X79 @ X80 )
      | ~ ( r2_hidden @ X77 @ X80 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X75: $i,X76: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X75 @ X76 ) )
      = ( k2_xboole_0 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('58',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','53','56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['58','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WuS1gpe1pj
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.90/3.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.90/3.14  % Solved by: fo/fo7.sh
% 2.90/3.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.90/3.14  % done 3688 iterations in 2.689s
% 2.90/3.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.90/3.14  % SZS output start Refutation
% 2.90/3.14  thf(sk_B_type, type, sk_B: $i).
% 2.90/3.14  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.90/3.14  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 2.90/3.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.90/3.14  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 2.90/3.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.90/3.14  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 2.90/3.14  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 2.90/3.14                                           $i > $i).
% 2.90/3.14  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.90/3.14  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.90/3.14  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.90/3.14  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.90/3.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.90/3.14  thf(sk_A_type, type, sk_A: $i).
% 2.90/3.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.90/3.14  thf(t45_zfmisc_1, conjecture,
% 2.90/3.14    (![A:$i,B:$i]:
% 2.90/3.14     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 2.90/3.14       ( r2_hidden @ A @ B ) ))).
% 2.90/3.14  thf(zf_stmt_0, negated_conjecture,
% 2.90/3.14    (~( ![A:$i,B:$i]:
% 2.90/3.14        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 2.90/3.14          ( r2_hidden @ A @ B ) ) )),
% 2.90/3.14    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 2.90/3.14  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 2.90/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.90/3.14  thf('1', plain,
% 2.90/3.14      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 2.90/3.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.90/3.14  thf(t28_xboole_1, axiom,
% 2.90/3.14    (![A:$i,B:$i]:
% 2.90/3.14     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.90/3.14  thf('2', plain,
% 2.90/3.14      (![X5 : $i, X6 : $i]:
% 2.90/3.14         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 2.90/3.14      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.90/3.14  thf('3', plain,
% 2.90/3.14      (((k3_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)
% 2.90/3.14         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 2.90/3.14      inference('sup-', [status(thm)], ['1', '2'])).
% 2.90/3.14  thf(commutativity_k3_xboole_0, axiom,
% 2.90/3.14    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.90/3.14  thf('4', plain,
% 2.90/3.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.90/3.14      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.90/3.14  thf('5', plain,
% 2.90/3.14      (((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 2.90/3.14         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 2.90/3.14      inference('demod', [status(thm)], ['3', '4'])).
% 2.90/3.14  thf(t72_enumset1, axiom,
% 2.90/3.14    (![A:$i,B:$i,C:$i,D:$i]:
% 2.90/3.14     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 2.90/3.14  thf('6', plain,
% 2.90/3.14      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 2.90/3.14         ((k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56)
% 2.90/3.14           = (k2_enumset1 @ X53 @ X54 @ X55 @ X56))),
% 2.90/3.14      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.90/3.14  thf(t71_enumset1, axiom,
% 2.90/3.14    (![A:$i,B:$i,C:$i]:
% 2.90/3.14     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.90/3.14  thf('7', plain,
% 2.90/3.14      (![X50 : $i, X51 : $i, X52 : $i]:
% 2.90/3.14         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 2.90/3.14           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 2.90/3.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.90/3.14  thf(t125_enumset1, axiom,
% 2.90/3.14    (![A:$i,B:$i,C:$i,D:$i]:
% 2.90/3.14     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 2.90/3.14  thf('8', plain,
% 2.90/3.14      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 2.90/3.14         ((k2_enumset1 @ X20 @ X19 @ X18 @ X17)
% 2.90/3.14           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 2.90/3.14      inference('cnf', [status(esa)], [t125_enumset1])).
% 2.90/3.14  thf('9', plain,
% 2.90/3.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.90/3.14         ((k2_enumset1 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.90/3.14      inference('sup+', [status(thm)], ['7', '8'])).
% 2.90/3.14  thf('10', plain,
% 2.90/3.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.90/3.14         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X0) = (k1_enumset1 @ X0 @ X1 @ X2))),
% 2.90/3.14      inference('sup+', [status(thm)], ['6', '9'])).
% 2.90/3.14  thf(t70_enumset1, axiom,
% 2.90/3.14    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.90/3.14  thf('11', plain,
% 2.90/3.14      (![X48 : $i, X49 : $i]:
% 2.90/3.14         ((k1_enumset1 @ X48 @ X48 @ X49) = (k2_tarski @ X48 @ X49))),
% 2.90/3.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.90/3.14  thf('12', plain,
% 2.90/3.14      (![X0 : $i, X1 : $i]:
% 2.90/3.14         ((k3_enumset1 @ X1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 2.90/3.14      inference('sup+', [status(thm)], ['10', '11'])).
% 2.90/3.14  thf('13', plain,
% 2.90/3.14      (![X48 : $i, X49 : $i]:
% 2.90/3.14         ((k1_enumset1 @ X48 @ X48 @ X49) = (k2_tarski @ X48 @ X49))),
% 2.90/3.14      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.90/3.14  thf(t69_enumset1, axiom,
% 2.90/3.14    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.90/3.14  thf('14', plain,
% 2.90/3.14      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 2.90/3.14      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.90/3.14  thf('15', plain,
% 2.90/3.14      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.90/3.14      inference('sup+', [status(thm)], ['13', '14'])).
% 2.90/3.14  thf(t75_enumset1, axiom,
% 2.90/3.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 2.90/3.14     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 2.90/3.14       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 2.90/3.14  thf('16', plain,
% 2.90/3.14      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i]:
% 2.90/3.14         ((k6_enumset1 @ X68 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74)
% 2.90/3.14           = (k5_enumset1 @ X68 @ X69 @ X70 @ X71 @ X72 @ X73 @ X74))),
% 2.90/3.14      inference('cnf', [status(esa)], [t75_enumset1])).
% 2.90/3.14  thf(l75_enumset1, axiom,
% 2.90/3.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 2.90/3.14     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 2.90/3.14       ( k2_xboole_0 @
% 2.90/3.14         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 2.90/3.14  thf('17', plain,
% 2.90/3.14      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 2.90/3.14         X16 : $i]:
% 2.90/3.14         ((k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 2.90/3.14           = (k2_xboole_0 @ (k2_enumset1 @ X9 @ X10 @ X11 @ X12) @ 
% 2.90/3.14              (k2_enumset1 @ X13 @ X14 @ X15 @ X16)))),
% 2.90/3.14      inference('cnf', [status(esa)], [l75_enumset1])).
% 2.90/3.14  thf(t7_xboole_1, axiom,
% 2.90/3.14    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.90/3.14  thf('18', plain,
% 2.90/3.14      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 2.90/3.14      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.90/3.14  thf('19', plain,
% 2.90/3.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.90/3.14         (r1_tarski @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 2.90/3.14          (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.90/3.14      inference('sup+', [status(thm)], ['17', '18'])).
% 2.90/3.14  thf('20', plain,
% 2.90/3.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.90/3.14         (r1_tarski @ (k2_enumset1 @ X6 @ X6 @ X5 @ X4) @ 
% 2.90/3.14          (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.90/3.14      inference('sup+', [status(thm)], ['16', '19'])).
% 2.90/3.14  thf('21', plain,
% 2.90/3.14      (![X50 : $i, X51 : $i, X52 : $i]:
% 2.90/3.14         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 2.90/3.14           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 2.90/3.14      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.90/3.14  thf('22', plain,
% 2.90/3.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.90/3.14         (r1_tarski @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 2.90/3.14          (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 2.90/3.14      inference('demod', [status(thm)], ['20', '21'])).
% 2.90/3.14  thf('23', plain,
% 2.90/3.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.90/3.14         (r1_tarski @ (k1_tarski @ X0) @ 
% 2.90/3.14          (k5_enumset1 @ X0 @ X0 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 2.90/3.14      inference('sup+', [status(thm)], ['15', '22'])).
% 2.90/3.14  thf(t74_enumset1, axiom,
% 2.90/3.14    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.90/3.14     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 2.90/3.14       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 2.90/3.14  thf('24', plain,
% 2.90/3.14      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i, X66 : $i, X67 : $i]:
% 2.90/3.14         ((k5_enumset1 @ X62 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67)
% 2.90/3.14           = (k4_enumset1 @ X62 @ X63 @ X64 @ X65 @ X66 @ X67))),
% 2.90/3.14      inference('cnf', [status(esa)], [t74_enumset1])).
% 2.90/3.14  thf(t73_enumset1, axiom,
% 2.90/3.14    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.90/3.14     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 2.90/3.14       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 2.90/3.14  thf('25', plain,
% 2.90/3.14      (![X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 2.90/3.15         ((k4_enumset1 @ X57 @ X57 @ X58 @ X59 @ X60 @ X61)
% 2.90/3.15           = (k3_enumset1 @ X57 @ X58 @ X59 @ X60 @ X61))),
% 2.90/3.15      inference('cnf', [status(esa)], [t73_enumset1])).
% 2.90/3.15  thf('26', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.90/3.15         (r1_tarski @ (k1_tarski @ X0) @ (k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 2.90/3.15      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.90/3.15  thf('27', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 2.90/3.15      inference('sup+', [status(thm)], ['12', '26'])).
% 2.90/3.15  thf('28', plain,
% 2.90/3.15      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 2.90/3.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.90/3.15  thf(t38_zfmisc_1, axiom,
% 2.90/3.15    (![A:$i,B:$i,C:$i]:
% 2.90/3.15     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 2.90/3.15       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 2.90/3.15  thf('29', plain,
% 2.90/3.15      (![X77 : $i, X78 : $i, X79 : $i]:
% 2.90/3.15         ((r2_hidden @ X77 @ X78)
% 2.90/3.15          | ~ (r1_tarski @ (k2_tarski @ X77 @ X79) @ X78))),
% 2.90/3.15      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 2.90/3.15  thf('30', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 2.90/3.15      inference('sup-', [status(thm)], ['28', '29'])).
% 2.90/3.15  thf('31', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 2.90/3.15      inference('sup-', [status(thm)], ['27', '30'])).
% 2.90/3.15  thf('32', plain,
% 2.90/3.15      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 2.90/3.15         ((k3_enumset1 @ X53 @ X53 @ X54 @ X55 @ X56)
% 2.90/3.15           = (k2_enumset1 @ X53 @ X54 @ X55 @ X56))),
% 2.90/3.15      inference('cnf', [status(esa)], [t72_enumset1])).
% 2.90/3.15  thf('33', plain,
% 2.90/3.15      (![X50 : $i, X51 : $i, X52 : $i]:
% 2.90/3.15         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 2.90/3.15           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 2.90/3.15      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.90/3.15  thf('34', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.90/3.15         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.90/3.15      inference('sup+', [status(thm)], ['32', '33'])).
% 2.90/3.15  thf('35', plain,
% 2.90/3.15      (![X48 : $i, X49 : $i]:
% 2.90/3.15         ((k1_enumset1 @ X48 @ X48 @ X49) = (k2_tarski @ X48 @ X49))),
% 2.90/3.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.90/3.15  thf('36', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 2.90/3.15      inference('sup+', [status(thm)], ['34', '35'])).
% 2.90/3.15  thf('37', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.90/3.15         (r1_tarski @ (k1_tarski @ X0) @ (k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 2.90/3.15      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.90/3.15  thf('38', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 2.90/3.15      inference('sup+', [status(thm)], ['36', '37'])).
% 2.90/3.15  thf('39', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 2.90/3.15      inference('sup-', [status(thm)], ['28', '29'])).
% 2.90/3.15  thf('40', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 2.90/3.15      inference('sup-', [status(thm)], ['38', '39'])).
% 2.90/3.15  thf('41', plain,
% 2.90/3.15      (![X77 : $i, X79 : $i, X80 : $i]:
% 2.90/3.15         ((r1_tarski @ (k2_tarski @ X77 @ X79) @ X80)
% 2.90/3.15          | ~ (r2_hidden @ X79 @ X80)
% 2.90/3.15          | ~ (r2_hidden @ X77 @ X80))),
% 2.90/3.15      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 2.90/3.15  thf('42', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.90/3.15         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.90/3.15          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X1 @ X0)))),
% 2.90/3.15      inference('sup-', [status(thm)], ['40', '41'])).
% 2.90/3.15  thf('43', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 2.90/3.15      inference('sup-', [status(thm)], ['31', '42'])).
% 2.90/3.15  thf('44', plain,
% 2.90/3.15      (![X5 : $i, X6 : $i]:
% 2.90/3.15         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 2.90/3.15      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.90/3.15  thf('45', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         ((k3_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))
% 2.90/3.15           = (k2_tarski @ X0 @ X1))),
% 2.90/3.15      inference('sup-', [status(thm)], ['43', '44'])).
% 2.90/3.15  thf('46', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.90/3.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.90/3.15  thf('47', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         ((k3_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))
% 2.90/3.15           = (k2_tarski @ X1 @ X0))),
% 2.90/3.15      inference('sup+', [status(thm)], ['45', '46'])).
% 2.90/3.15  thf('48', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         ((k3_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))
% 2.90/3.15           = (k2_tarski @ X0 @ X1))),
% 2.90/3.15      inference('sup-', [status(thm)], ['43', '44'])).
% 2.90/3.15  thf('49', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 2.90/3.15      inference('sup+', [status(thm)], ['47', '48'])).
% 2.90/3.15  thf(l51_zfmisc_1, axiom,
% 2.90/3.15    (![A:$i,B:$i]:
% 2.90/3.15     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.90/3.15  thf('50', plain,
% 2.90/3.15      (![X75 : $i, X76 : $i]:
% 2.90/3.15         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 2.90/3.15      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.90/3.15  thf('51', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 2.90/3.15      inference('sup+', [status(thm)], ['49', '50'])).
% 2.90/3.15  thf('52', plain,
% 2.90/3.15      (![X75 : $i, X76 : $i]:
% 2.90/3.15         ((k3_tarski @ (k2_tarski @ X75 @ X76)) = (k2_xboole_0 @ X75 @ X76))),
% 2.90/3.15      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.90/3.15  thf('53', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.90/3.15      inference('sup+', [status(thm)], ['51', '52'])).
% 2.90/3.15  thf('54', plain,
% 2.90/3.15      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 2.90/3.15      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.90/3.15  thf('55', plain,
% 2.90/3.15      (![X5 : $i, X6 : $i]:
% 2.90/3.15         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 2.90/3.15      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.90/3.15  thf('56', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 2.90/3.15      inference('sup-', [status(thm)], ['54', '55'])).
% 2.90/3.15  thf('57', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.90/3.15      inference('sup+', [status(thm)], ['51', '52'])).
% 2.90/3.15  thf('58', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.90/3.15      inference('demod', [status(thm)], ['5', '53', '56', '57'])).
% 2.90/3.15  thf('59', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.90/3.15         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 2.90/3.15      inference('sup+', [status(thm)], ['32', '33'])).
% 2.90/3.15  thf('60', plain,
% 2.90/3.15      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.90/3.15      inference('sup+', [status(thm)], ['13', '14'])).
% 2.90/3.15  thf('61', plain,
% 2.90/3.15      (![X0 : $i]: ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 2.90/3.15      inference('sup+', [status(thm)], ['59', '60'])).
% 2.90/3.15  thf('62', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.90/3.15         (r1_tarski @ (k1_tarski @ X0) @ (k3_enumset1 @ X0 @ X4 @ X3 @ X2 @ X1))),
% 2.90/3.15      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.90/3.15  thf('63', plain,
% 2.90/3.15      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 2.90/3.15      inference('sup+', [status(thm)], ['61', '62'])).
% 2.90/3.15  thf(t10_xboole_1, axiom,
% 2.90/3.15    (![A:$i,B:$i,C:$i]:
% 2.90/3.15     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.90/3.15  thf('64', plain,
% 2.90/3.15      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.90/3.15         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 2.90/3.15      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.90/3.15  thf('65', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         (r1_tarski @ (k1_tarski @ X0) @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.90/3.15      inference('sup-', [status(thm)], ['63', '64'])).
% 2.90/3.15  thf('66', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 2.90/3.15      inference('sup-', [status(thm)], ['28', '29'])).
% 2.90/3.15  thf('67', plain,
% 2.90/3.15      (![X0 : $i, X1 : $i]:
% 2.90/3.15         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.90/3.15      inference('sup-', [status(thm)], ['65', '66'])).
% 2.90/3.15  thf('68', plain, ((r2_hidden @ sk_A @ sk_B)),
% 2.90/3.15      inference('sup+', [status(thm)], ['58', '67'])).
% 2.90/3.15  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 2.90/3.15  
% 2.90/3.15  % SZS output end Refutation
% 2.90/3.15  
% 2.90/3.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
