%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pca8mToELO

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:41 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 621 expanded)
%              Number of leaves         :   32 ( 208 expanded)
%              Depth                    :   26
%              Number of atoms          : 1257 (4406 expanded)
%              Number of equality atoms :   92 ( 355 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('0',plain,(
    ! [X50: $i] :
      ( r2_hidden @ X50 @ ( k1_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k1_ordinal1 @ A )
        = ( k1_ordinal1 @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k1_ordinal1 @ A )
          = ( k1_ordinal1 @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_ordinal1])).

thf('3',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X48 ) )
        = X47 )
      | ( r2_hidden @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_xboole_0 @ X35 @ X37 )
      | ( ( k4_xboole_0 @ X35 @ X37 )
       != X35 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('8',plain,(
    ! [X49: $i] :
      ( ( k1_ordinal1 @ X49 )
      = ( k2_xboole_0 @ X49 @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_tarski @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) )
      | ~ ( r1_xboole_0 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X47: $i,X48: $i] :
      ( ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X48 ) )
        = X47 )
      | ( r2_hidden @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k3_xboole_0 @ X26 @ X27 ) )
      = ( k4_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X46 @ X47 )
      | ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X46 ) )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('39',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('40',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X49: $i] :
      ( ( k1_ordinal1 @ X49 )
      = ( k2_xboole_0 @ X49 @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    = ( k1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k1_ordinal1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','49'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ ( k1_ordinal1 @ sk_A ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,
    ( ( k3_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k3_xboole_0 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['37','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_ordinal1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('64',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('66',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('68',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('73',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('75',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('77',plain,
    ( ( k1_ordinal1 @ sk_A )
    = ( k1_ordinal1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X50: $i] :
      ( r2_hidden @ X50 @ ( k1_ordinal1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('79',plain,(
    r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('81',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('83',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ X23 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k2_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('87',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['76','87'])).

thf('89',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('90',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('91',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('92',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','92'])).

thf('94',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('96',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['70','101'])).

thf('103',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('104',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('105',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['102','107'])).

thf('109',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('110',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,
    ( ( k1_tarski @ sk_A )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['61','114'])).

thf('116',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_xboole_0 @ X35 @ X37 )
      | ( ( k4_xboole_0 @ X35 @ X37 )
       != X35 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('117',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('120',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_tarski @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) )
      | ~ ( r1_xboole_0 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['118','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('129',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('131',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('137',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X46 @ X47 )
      | ( ( k4_xboole_0 @ X47 @ ( k1_tarski @ X46 ) )
       != X47 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('140',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ ( k1_tarski @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['138','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['135','143'])).

thf('145',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['124','144'])).

thf('146',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['36','145'])).

thf('147',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('148',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['70','101'])).

thf('150',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('151',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup+',[status(thm)],['149','152'])).

thf('154',plain,(
    $false ),
    inference(demod,[status(thm)],['148','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pca8mToELO
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:40:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.42/1.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.42/1.68  % Solved by: fo/fo7.sh
% 1.42/1.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.42/1.68  % done 3726 iterations in 1.226s
% 1.42/1.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.42/1.68  % SZS output start Refutation
% 1.42/1.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.42/1.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.42/1.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.42/1.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.42/1.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.42/1.68  thf(sk_A_type, type, sk_A: $i).
% 1.42/1.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.42/1.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.42/1.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.42/1.68  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.42/1.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.42/1.68  thf(sk_B_type, type, sk_B: $i).
% 1.42/1.68  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 1.42/1.68  thf('0', plain, (![X50 : $i]: (r2_hidden @ X50 @ (k1_ordinal1 @ X50))),
% 1.42/1.68      inference('cnf', [status(esa)], [t10_ordinal1])).
% 1.42/1.68  thf(l1_zfmisc_1, axiom,
% 1.42/1.68    (![A:$i,B:$i]:
% 1.42/1.68     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.42/1.68  thf('1', plain,
% 1.42/1.68      (![X41 : $i, X43 : $i]:
% 1.42/1.68         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 1.42/1.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.42/1.68  thf('2', plain,
% 1.42/1.68      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['0', '1'])).
% 1.42/1.68  thf(t12_ordinal1, conjecture,
% 1.42/1.68    (![A:$i,B:$i]:
% 1.42/1.68     ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ))).
% 1.42/1.68  thf(zf_stmt_0, negated_conjecture,
% 1.42/1.68    (~( ![A:$i,B:$i]:
% 1.42/1.68        ( ( ( k1_ordinal1 @ A ) = ( k1_ordinal1 @ B ) ) => ( ( A ) = ( B ) ) ) )),
% 1.42/1.68    inference('cnf.neg', [status(esa)], [t12_ordinal1])).
% 1.42/1.68  thf('3', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 1.42/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.68  thf(t65_zfmisc_1, axiom,
% 1.42/1.68    (![A:$i,B:$i]:
% 1.42/1.68     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.42/1.68       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.42/1.68  thf('4', plain,
% 1.42/1.68      (![X47 : $i, X48 : $i]:
% 1.42/1.68         (((k4_xboole_0 @ X47 @ (k1_tarski @ X48)) = (X47))
% 1.42/1.68          | (r2_hidden @ X48 @ X47))),
% 1.42/1.68      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.42/1.68  thf(t83_xboole_1, axiom,
% 1.42/1.68    (![A:$i,B:$i]:
% 1.42/1.68     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.42/1.68  thf('5', plain,
% 1.42/1.68      (![X35 : $i, X37 : $i]:
% 1.42/1.68         ((r1_xboole_0 @ X35 @ X37) | ((k4_xboole_0 @ X35 @ X37) != (X35)))),
% 1.42/1.68      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.42/1.68  thf('6', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (((X0) != (X0))
% 1.42/1.68          | (r2_hidden @ X1 @ X0)
% 1.42/1.68          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['4', '5'])).
% 1.42/1.68  thf('7', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 1.42/1.68      inference('simplify', [status(thm)], ['6'])).
% 1.42/1.68  thf(d1_ordinal1, axiom,
% 1.42/1.68    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 1.42/1.68  thf('8', plain,
% 1.42/1.68      (![X49 : $i]:
% 1.42/1.68         ((k1_ordinal1 @ X49) = (k2_xboole_0 @ X49 @ (k1_tarski @ X49)))),
% 1.42/1.68      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.42/1.68  thf(t73_xboole_1, axiom,
% 1.42/1.68    (![A:$i,B:$i,C:$i]:
% 1.42/1.68     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.42/1.68       ( r1_tarski @ A @ B ) ))).
% 1.42/1.68  thf('9', plain,
% 1.42/1.68      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.42/1.68         ((r1_tarski @ X30 @ X31)
% 1.42/1.68          | ~ (r1_tarski @ X30 @ (k2_xboole_0 @ X31 @ X32))
% 1.42/1.68          | ~ (r1_xboole_0 @ X30 @ X32))),
% 1.42/1.68      inference('cnf', [status(esa)], [t73_xboole_1])).
% 1.42/1.68  thf('10', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 1.42/1.68          | ~ (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.42/1.68          | (r1_tarski @ X1 @ X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['8', '9'])).
% 1.42/1.68  thf('11', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         ((r2_hidden @ X0 @ X1)
% 1.42/1.68          | (r1_tarski @ X1 @ X0)
% 1.42/1.68          | ~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['7', '10'])).
% 1.42/1.68  thf('12', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         (~ (r1_tarski @ X0 @ (k1_ordinal1 @ sk_A))
% 1.42/1.68          | (r1_tarski @ X0 @ sk_B)
% 1.42/1.68          | (r2_hidden @ sk_B @ X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['3', '11'])).
% 1.42/1.68  thf('13', plain,
% 1.42/1.68      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 1.42/1.68        | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.42/1.68      inference('sup-', [status(thm)], ['2', '12'])).
% 1.42/1.68  thf('14', plain,
% 1.42/1.68      (![X47 : $i, X48 : $i]:
% 1.42/1.68         (((k4_xboole_0 @ X47 @ (k1_tarski @ X48)) = (X47))
% 1.42/1.68          | (r2_hidden @ X48 @ X47))),
% 1.42/1.68      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.42/1.68  thf(t48_xboole_1, axiom,
% 1.42/1.68    (![A:$i,B:$i]:
% 1.42/1.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.42/1.68  thf('15', plain,
% 1.42/1.68      (![X28 : $i, X29 : $i]:
% 1.42/1.68         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 1.42/1.68           = (k3_xboole_0 @ X28 @ X29))),
% 1.42/1.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.68  thf('16', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.42/1.68          | (r2_hidden @ X1 @ X0))),
% 1.42/1.68      inference('sup+', [status(thm)], ['14', '15'])).
% 1.42/1.68  thf(t7_xboole_1, axiom,
% 1.42/1.68    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.42/1.68  thf('17', plain,
% 1.42/1.68      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 1.42/1.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.42/1.68  thf(t43_xboole_1, axiom,
% 1.42/1.68    (![A:$i,B:$i,C:$i]:
% 1.42/1.68     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.42/1.68       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.42/1.68  thf('18', plain,
% 1.42/1.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.42/1.68         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 1.42/1.68          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 1.42/1.68      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.42/1.68  thf('19', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 1.42/1.68      inference('sup-', [status(thm)], ['17', '18'])).
% 1.42/1.68  thf(t3_boole, axiom,
% 1.42/1.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.42/1.68  thf('20', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.42/1.68      inference('cnf', [status(esa)], [t3_boole])).
% 1.42/1.68  thf('21', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 1.42/1.68      inference('sup-', [status(thm)], ['17', '18'])).
% 1.42/1.68  thf('22', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.42/1.68      inference('sup+', [status(thm)], ['20', '21'])).
% 1.42/1.68  thf(d10_xboole_0, axiom,
% 1.42/1.68    (![A:$i,B:$i]:
% 1.42/1.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.42/1.68  thf('23', plain,
% 1.42/1.68      (![X10 : $i, X12 : $i]:
% 1.42/1.68         (((X10) = (X12))
% 1.42/1.68          | ~ (r1_tarski @ X12 @ X10)
% 1.42/1.68          | ~ (r1_tarski @ X10 @ X12))),
% 1.42/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.42/1.68  thf('24', plain,
% 1.42/1.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['22', '23'])).
% 1.42/1.68  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['19', '24'])).
% 1.42/1.68  thf('26', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 1.42/1.68          | (r2_hidden @ X1 @ X0))),
% 1.42/1.68      inference('demod', [status(thm)], ['16', '25'])).
% 1.42/1.68  thf(commutativity_k3_xboole_0, axiom,
% 1.42/1.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.42/1.68  thf('27', plain,
% 1.42/1.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.42/1.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.42/1.68  thf(t47_xboole_1, axiom,
% 1.42/1.68    (![A:$i,B:$i]:
% 1.42/1.68     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.42/1.68  thf('28', plain,
% 1.42/1.68      (![X26 : $i, X27 : $i]:
% 1.42/1.68         ((k4_xboole_0 @ X26 @ (k3_xboole_0 @ X26 @ X27))
% 1.42/1.68           = (k4_xboole_0 @ X26 @ X27))),
% 1.42/1.68      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.42/1.68  thf('29', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.42/1.68           = (k4_xboole_0 @ X0 @ X1))),
% 1.42/1.68      inference('sup+', [status(thm)], ['27', '28'])).
% 1.42/1.68  thf('30', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (((k4_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0)
% 1.42/1.68            = (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.42/1.68          | (r2_hidden @ X1 @ X0))),
% 1.42/1.68      inference('sup+', [status(thm)], ['26', '29'])).
% 1.42/1.68  thf('31', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.42/1.68      inference('cnf', [status(esa)], [t3_boole])).
% 1.42/1.68  thf('32', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.42/1.68          | (r2_hidden @ X1 @ X0))),
% 1.42/1.68      inference('demod', [status(thm)], ['30', '31'])).
% 1.42/1.68  thf('33', plain,
% 1.42/1.68      (![X46 : $i, X47 : $i]:
% 1.42/1.68         (~ (r2_hidden @ X46 @ X47)
% 1.42/1.68          | ((k4_xboole_0 @ X47 @ (k1_tarski @ X46)) != (X47)))),
% 1.42/1.68      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.42/1.68  thf('34', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 1.42/1.68          | (r2_hidden @ X0 @ (k1_tarski @ X1))
% 1.42/1.68          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['32', '33'])).
% 1.42/1.68  thf('35', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.42/1.68          | (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 1.42/1.68      inference('simplify', [status(thm)], ['34'])).
% 1.42/1.68  thf('36', plain,
% 1.42/1.68      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)
% 1.42/1.68        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['13', '35'])).
% 1.42/1.68  thf('37', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.42/1.68          | (r2_hidden @ X1 @ X0))),
% 1.42/1.68      inference('demod', [status(thm)], ['30', '31'])).
% 1.42/1.68  thf('38', plain,
% 1.42/1.68      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['0', '1'])).
% 1.42/1.68  thf('39', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 1.42/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.68  thf(t69_enumset1, axiom,
% 1.42/1.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.42/1.68  thf('40', plain,
% 1.42/1.68      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 1.42/1.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.42/1.68  thf('41', plain,
% 1.42/1.68      (![X49 : $i]:
% 1.42/1.68         ((k1_ordinal1 @ X49) = (k2_xboole_0 @ X49 @ (k1_tarski @ X49)))),
% 1.42/1.68      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.42/1.68  thf('42', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 1.42/1.68      inference('sup+', [status(thm)], ['40', '41'])).
% 1.42/1.68  thf('43', plain,
% 1.42/1.68      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 1.42/1.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.42/1.68  thf('44', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 1.42/1.68      inference('sup+', [status(thm)], ['42', '43'])).
% 1.42/1.68  thf('45', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 1.42/1.68      inference('sup+', [status(thm)], ['39', '44'])).
% 1.42/1.68  thf(t12_xboole_1, axiom,
% 1.42/1.68    (![A:$i,B:$i]:
% 1.42/1.68     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.42/1.68  thf('46', plain,
% 1.42/1.68      (![X13 : $i, X14 : $i]:
% 1.42/1.68         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 1.42/1.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.42/1.68  thf('47', plain,
% 1.42/1.68      (((k2_xboole_0 @ sk_B @ (k1_ordinal1 @ sk_A)) = (k1_ordinal1 @ sk_A))),
% 1.42/1.68      inference('sup-', [status(thm)], ['45', '46'])).
% 1.42/1.68  thf('48', plain,
% 1.42/1.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.42/1.68         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 1.42/1.68          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 1.42/1.68      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.42/1.68  thf('49', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         (~ (r1_tarski @ X0 @ (k1_ordinal1 @ sk_A))
% 1.42/1.68          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_B) @ (k1_ordinal1 @ sk_A)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['47', '48'])).
% 1.42/1.68  thf('50', plain,
% 1.42/1.68      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 1.42/1.68        (k1_ordinal1 @ sk_A))),
% 1.42/1.68      inference('sup-', [status(thm)], ['38', '49'])).
% 1.42/1.68  thf(t28_xboole_1, axiom,
% 1.42/1.68    (![A:$i,B:$i]:
% 1.42/1.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.42/1.68  thf('51', plain,
% 1.42/1.68      (![X15 : $i, X16 : $i]:
% 1.42/1.68         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.42/1.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.42/1.68  thf('52', plain,
% 1.42/1.68      (((k3_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ 
% 1.42/1.68         (k1_ordinal1 @ sk_A)) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 1.42/1.68      inference('sup-', [status(thm)], ['50', '51'])).
% 1.42/1.68  thf('53', plain,
% 1.42/1.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.42/1.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.42/1.68  thf('54', plain,
% 1.42/1.68      (((k3_xboole_0 @ (k1_ordinal1 @ sk_A) @ 
% 1.42/1.68         (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 1.42/1.68         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 1.42/1.68      inference('demod', [status(thm)], ['52', '53'])).
% 1.42/1.68  thf('55', plain,
% 1.42/1.68      ((((k3_xboole_0 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A))
% 1.42/1.68          = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 1.42/1.68        | (r2_hidden @ sk_A @ sk_B))),
% 1.42/1.68      inference('sup+', [status(thm)], ['37', '54'])).
% 1.42/1.68  thf('56', plain,
% 1.42/1.68      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['0', '1'])).
% 1.42/1.68  thf('57', plain,
% 1.42/1.68      (![X15 : $i, X16 : $i]:
% 1.42/1.68         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.42/1.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.42/1.68  thf('58', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))
% 1.42/1.68           = (k1_tarski @ X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['56', '57'])).
% 1.42/1.68  thf('59', plain,
% 1.42/1.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.42/1.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.42/1.68  thf('60', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         ((k3_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0))
% 1.42/1.68           = (k1_tarski @ X0))),
% 1.42/1.68      inference('demod', [status(thm)], ['58', '59'])).
% 1.42/1.68  thf('61', plain,
% 1.42/1.68      ((((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 1.42/1.68        | (r2_hidden @ sk_A @ sk_B))),
% 1.42/1.68      inference('demod', [status(thm)], ['55', '60'])).
% 1.42/1.68  thf('62', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 1.42/1.68      inference('sup+', [status(thm)], ['42', '43'])).
% 1.42/1.68  thf('63', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         (~ (r1_tarski @ X0 @ (k1_ordinal1 @ sk_A))
% 1.42/1.68          | (r1_tarski @ X0 @ sk_B)
% 1.42/1.68          | (r2_hidden @ sk_B @ X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['3', '11'])).
% 1.42/1.68  thf('64', plain, (((r2_hidden @ sk_B @ sk_A) | (r1_tarski @ sk_A @ sk_B))),
% 1.42/1.68      inference('sup-', [status(thm)], ['62', '63'])).
% 1.42/1.68  thf('65', plain,
% 1.42/1.68      (![X41 : $i, X43 : $i]:
% 1.42/1.68         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 1.42/1.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.42/1.68  thf('66', plain,
% 1.42/1.68      (((r1_tarski @ sk_A @ sk_B) | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 1.42/1.68      inference('sup-', [status(thm)], ['64', '65'])).
% 1.42/1.68  thf('67', plain,
% 1.42/1.68      (![X15 : $i, X16 : $i]:
% 1.42/1.68         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.42/1.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.42/1.68  thf('68', plain,
% 1.42/1.68      (((r1_tarski @ sk_A @ sk_B)
% 1.42/1.68        | ((k3_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tarski @ sk_B)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['66', '67'])).
% 1.42/1.68  thf('69', plain,
% 1.42/1.68      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.42/1.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.42/1.68  thf('70', plain,
% 1.42/1.68      (((r1_tarski @ sk_A @ sk_B)
% 1.42/1.68        | ((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B)))),
% 1.42/1.68      inference('demod', [status(thm)], ['68', '69'])).
% 1.42/1.68  thf('71', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 1.42/1.68      inference('sup+', [status(thm)], ['39', '44'])).
% 1.42/1.68  thf('72', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         ((r2_hidden @ X0 @ X1)
% 1.42/1.68          | (r1_tarski @ X1 @ X0)
% 1.42/1.68          | ~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['7', '10'])).
% 1.42/1.68  thf('73', plain, (((r1_tarski @ sk_B @ sk_A) | (r2_hidden @ sk_A @ sk_B))),
% 1.42/1.68      inference('sup-', [status(thm)], ['71', '72'])).
% 1.42/1.68  thf('74', plain,
% 1.42/1.68      (![X41 : $i, X43 : $i]:
% 1.42/1.68         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 1.42/1.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.42/1.68  thf('75', plain,
% 1.42/1.68      (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.42/1.68      inference('sup-', [status(thm)], ['73', '74'])).
% 1.42/1.68  thf('76', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (((k1_tarski @ X1) = (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 1.42/1.68          | (r2_hidden @ X1 @ X0))),
% 1.42/1.68      inference('demod', [status(thm)], ['30', '31'])).
% 1.42/1.68  thf('77', plain, (((k1_ordinal1 @ sk_A) = (k1_ordinal1 @ sk_B))),
% 1.42/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.68  thf('78', plain, (![X50 : $i]: (r2_hidden @ X50 @ (k1_ordinal1 @ X50))),
% 1.42/1.68      inference('cnf', [status(esa)], [t10_ordinal1])).
% 1.42/1.68  thf('79', plain, ((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))),
% 1.42/1.68      inference('sup+', [status(thm)], ['77', '78'])).
% 1.42/1.68  thf('80', plain,
% 1.42/1.68      (![X41 : $i, X43 : $i]:
% 1.42/1.68         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 1.42/1.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.42/1.68  thf('81', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ (k1_ordinal1 @ sk_A))),
% 1.42/1.68      inference('sup-', [status(thm)], ['79', '80'])).
% 1.42/1.68  thf('82', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 1.42/1.68      inference('sup+', [status(thm)], ['40', '41'])).
% 1.42/1.68  thf('83', plain,
% 1.42/1.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.42/1.68         ((r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X25)
% 1.42/1.68          | ~ (r1_tarski @ X23 @ (k2_xboole_0 @ X24 @ X25)))),
% 1.42/1.68      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.42/1.68  thf('84', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (~ (r1_tarski @ X1 @ (k1_ordinal1 @ X0))
% 1.42/1.68          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k2_tarski @ X0 @ X0)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['82', '83'])).
% 1.42/1.68  thf('85', plain,
% 1.42/1.68      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 1.42/1.68        (k2_tarski @ sk_A @ sk_A))),
% 1.42/1.68      inference('sup-', [status(thm)], ['81', '84'])).
% 1.42/1.68  thf('86', plain,
% 1.42/1.68      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 1.42/1.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.42/1.68  thf('87', plain,
% 1.42/1.68      ((r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 1.42/1.68        (k1_tarski @ sk_A))),
% 1.42/1.68      inference('demod', [status(thm)], ['85', '86'])).
% 1.42/1.68  thf('88', plain,
% 1.42/1.68      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 1.42/1.68        | (r2_hidden @ sk_B @ sk_A))),
% 1.42/1.68      inference('sup+', [status(thm)], ['76', '87'])).
% 1.42/1.68  thf('89', plain,
% 1.42/1.68      (![X41 : $i, X42 : $i]:
% 1.42/1.68         ((r2_hidden @ X41 @ X42) | ~ (r1_tarski @ (k1_tarski @ X41) @ X42))),
% 1.42/1.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.42/1.68  thf('90', plain,
% 1.42/1.68      (((r2_hidden @ sk_B @ sk_A) | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['88', '89'])).
% 1.42/1.68  thf(t7_ordinal1, axiom,
% 1.42/1.68    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.42/1.68  thf('91', plain,
% 1.42/1.68      (![X51 : $i, X52 : $i]:
% 1.42/1.68         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 1.42/1.68      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.42/1.68  thf('92', plain,
% 1.42/1.68      (((r2_hidden @ sk_B @ sk_A) | ~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.42/1.68      inference('sup-', [status(thm)], ['90', '91'])).
% 1.42/1.68  thf('93', plain, (((r1_tarski @ sk_B @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 1.42/1.68      inference('sup-', [status(thm)], ['75', '92'])).
% 1.42/1.68  thf('94', plain, (((r1_tarski @ sk_B @ sk_A) | (r2_hidden @ sk_A @ sk_B))),
% 1.42/1.68      inference('sup-', [status(thm)], ['71', '72'])).
% 1.42/1.68  thf(antisymmetry_r2_hidden, axiom,
% 1.42/1.68    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 1.42/1.68  thf('95', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 1.42/1.68      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 1.42/1.68  thf('96', plain, (((r1_tarski @ sk_B @ sk_A) | ~ (r2_hidden @ sk_B @ sk_A))),
% 1.42/1.68      inference('sup-', [status(thm)], ['94', '95'])).
% 1.42/1.68  thf('97', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.42/1.68      inference('clc', [status(thm)], ['93', '96'])).
% 1.42/1.68  thf('98', plain,
% 1.42/1.68      (![X10 : $i, X12 : $i]:
% 1.42/1.68         (((X10) = (X12))
% 1.42/1.68          | ~ (r1_tarski @ X12 @ X10)
% 1.42/1.68          | ~ (r1_tarski @ X10 @ X12))),
% 1.42/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.42/1.68  thf('99', plain, ((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['97', '98'])).
% 1.42/1.68  thf('100', plain, (((sk_A) != (sk_B))),
% 1.42/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.68  thf('101', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 1.42/1.68      inference('simplify_reflect-', [status(thm)], ['99', '100'])).
% 1.42/1.68  thf('102', plain,
% 1.42/1.68      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 1.42/1.68      inference('clc', [status(thm)], ['70', '101'])).
% 1.42/1.68  thf('103', plain,
% 1.42/1.68      (![X28 : $i, X29 : $i]:
% 1.42/1.68         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 1.42/1.68           = (k3_xboole_0 @ X28 @ X29))),
% 1.42/1.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.68  thf(t36_xboole_1, axiom,
% 1.42/1.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.42/1.68  thf('104', plain,
% 1.42/1.68      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 1.42/1.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.42/1.68  thf('105', plain,
% 1.42/1.68      (![X13 : $i, X14 : $i]:
% 1.42/1.68         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 1.42/1.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.42/1.68  thf('106', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['104', '105'])).
% 1.42/1.68  thf('107', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 1.42/1.68      inference('sup+', [status(thm)], ['103', '106'])).
% 1.42/1.68  thf('108', plain, (((k2_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (sk_A))),
% 1.42/1.68      inference('sup+', [status(thm)], ['102', '107'])).
% 1.42/1.68  thf('109', plain,
% 1.42/1.68      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 1.42/1.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.42/1.68  thf('110', plain,
% 1.42/1.68      (![X41 : $i, X42 : $i]:
% 1.42/1.68         ((r2_hidden @ X41 @ X42) | ~ (r1_tarski @ (k1_tarski @ X41) @ X42))),
% 1.42/1.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.42/1.68  thf('111', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['109', '110'])).
% 1.42/1.68  thf('112', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 1.42/1.68      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 1.42/1.68  thf('113', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         ~ (r2_hidden @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X1)),
% 1.42/1.68      inference('sup-', [status(thm)], ['111', '112'])).
% 1.42/1.68  thf('114', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.42/1.68      inference('sup-', [status(thm)], ['108', '113'])).
% 1.42/1.68  thf('115', plain,
% 1.42/1.68      (((k1_tarski @ sk_A) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 1.42/1.68      inference('clc', [status(thm)], ['61', '114'])).
% 1.42/1.68  thf('116', plain,
% 1.42/1.68      (![X35 : $i, X37 : $i]:
% 1.42/1.68         ((r1_xboole_0 @ X35 @ X37) | ((k4_xboole_0 @ X35 @ X37) != (X35)))),
% 1.42/1.68      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.42/1.68  thf('117', plain,
% 1.42/1.68      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 1.42/1.68        | (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 1.42/1.68      inference('sup-', [status(thm)], ['115', '116'])).
% 1.42/1.68  thf('118', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.42/1.68      inference('simplify', [status(thm)], ['117'])).
% 1.42/1.68  thf('119', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.42/1.68      inference('sup+', [status(thm)], ['20', '21'])).
% 1.42/1.68  thf('120', plain,
% 1.42/1.68      (![X13 : $i, X14 : $i]:
% 1.42/1.68         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 1.42/1.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.42/1.68  thf('121', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['119', '120'])).
% 1.42/1.68  thf('122', plain,
% 1.42/1.68      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.42/1.68         ((r1_tarski @ X30 @ X31)
% 1.42/1.68          | ~ (r1_tarski @ X30 @ (k2_xboole_0 @ X31 @ X32))
% 1.42/1.68          | ~ (r1_xboole_0 @ X30 @ X32))),
% 1.42/1.68      inference('cnf', [status(esa)], [t73_xboole_1])).
% 1.42/1.68  thf('123', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (~ (r1_tarski @ X1 @ X0)
% 1.42/1.68          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.42/1.68          | (r1_tarski @ X1 @ k1_xboole_0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['121', '122'])).
% 1.42/1.68  thf('124', plain,
% 1.42/1.68      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 1.42/1.68        | ~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 1.42/1.68      inference('sup-', [status(thm)], ['118', '123'])).
% 1.42/1.68  thf('125', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         ((k3_xboole_0 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0))
% 1.42/1.68           = (k1_tarski @ X0))),
% 1.42/1.68      inference('demod', [status(thm)], ['58', '59'])).
% 1.42/1.68  thf('126', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.42/1.68           = (k4_xboole_0 @ X0 @ X1))),
% 1.42/1.68      inference('sup+', [status(thm)], ['27', '28'])).
% 1.42/1.68  thf('127', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 1.42/1.68           = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0)))),
% 1.42/1.68      inference('sup+', [status(thm)], ['125', '126'])).
% 1.42/1.68  thf('128', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['19', '24'])).
% 1.42/1.68  thf('129', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0)))),
% 1.42/1.68      inference('demod', [status(thm)], ['127', '128'])).
% 1.42/1.68  thf('130', plain,
% 1.42/1.68      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 1.42/1.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.42/1.68  thf('131', plain,
% 1.42/1.68      (![X10 : $i, X12 : $i]:
% 1.42/1.68         (((X10) = (X12))
% 1.42/1.68          | ~ (r1_tarski @ X12 @ X10)
% 1.42/1.68          | ~ (r1_tarski @ X10 @ X12))),
% 1.42/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.42/1.68  thf('132', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]:
% 1.42/1.68         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.42/1.68          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['130', '131'])).
% 1.42/1.68  thf('133', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 1.42/1.68          | ((k1_tarski @ X0)
% 1.42/1.68              = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))))),
% 1.42/1.68      inference('sup-', [status(thm)], ['129', '132'])).
% 1.42/1.68  thf('134', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         ((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0)))),
% 1.42/1.68      inference('demod', [status(thm)], ['127', '128'])).
% 1.42/1.68  thf('135', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 1.42/1.68          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.42/1.68      inference('demod', [status(thm)], ['133', '134'])).
% 1.42/1.68  thf('136', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['19', '24'])).
% 1.42/1.68  thf('137', plain,
% 1.42/1.68      (![X46 : $i, X47 : $i]:
% 1.42/1.68         (~ (r2_hidden @ X46 @ X47)
% 1.42/1.68          | ((k4_xboole_0 @ X47 @ (k1_tarski @ X46)) != (X47)))),
% 1.42/1.68      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.42/1.68  thf('138', plain,
% 1.42/1.68      (![X0 : $i]:
% 1.42/1.68         (((k1_xboole_0) != (k1_tarski @ X0))
% 1.42/1.68          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.42/1.68      inference('sup-', [status(thm)], ['136', '137'])).
% 1.42/1.68  thf('139', plain,
% 1.42/1.68      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 1.42/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.42/1.68  thf('140', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 1.42/1.68      inference('simplify', [status(thm)], ['139'])).
% 1.42/1.68  thf('141', plain,
% 1.42/1.68      (![X41 : $i, X42 : $i]:
% 1.42/1.68         ((r2_hidden @ X41 @ X42) | ~ (r1_tarski @ (k1_tarski @ X41) @ X42))),
% 1.42/1.68      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.42/1.68  thf('142', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.42/1.68      inference('sup-', [status(thm)], ['140', '141'])).
% 1.42/1.68  thf('143', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 1.42/1.68      inference('demod', [status(thm)], ['138', '142'])).
% 1.42/1.68  thf('144', plain,
% 1.42/1.68      (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)),
% 1.42/1.68      inference('clc', [status(thm)], ['135', '143'])).
% 1.42/1.68  thf('145', plain, (~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 1.42/1.68      inference('clc', [status(thm)], ['124', '144'])).
% 1.42/1.68  thf('146', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 1.42/1.68      inference('clc', [status(thm)], ['36', '145'])).
% 1.42/1.68  thf('147', plain,
% 1.42/1.68      (![X51 : $i, X52 : $i]:
% 1.42/1.68         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 1.42/1.68      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.42/1.68  thf('148', plain, (~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 1.42/1.68      inference('sup-', [status(thm)], ['146', '147'])).
% 1.42/1.68  thf('149', plain,
% 1.42/1.68      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 1.42/1.68      inference('clc', [status(thm)], ['70', '101'])).
% 1.42/1.68  thf('150', plain,
% 1.42/1.68      (![X28 : $i, X29 : $i]:
% 1.42/1.68         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 1.42/1.68           = (k3_xboole_0 @ X28 @ X29))),
% 1.42/1.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.68  thf('151', plain,
% 1.42/1.68      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 1.42/1.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.42/1.68  thf('152', plain,
% 1.42/1.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 1.42/1.68      inference('sup+', [status(thm)], ['150', '151'])).
% 1.42/1.68  thf('153', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 1.42/1.68      inference('sup+', [status(thm)], ['149', '152'])).
% 1.42/1.68  thf('154', plain, ($false), inference('demod', [status(thm)], ['148', '153'])).
% 1.42/1.68  
% 1.42/1.68  % SZS output end Refutation
% 1.42/1.68  
% 1.51/1.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
