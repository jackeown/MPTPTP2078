%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cSm7jJZbPa

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:58 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 745 expanded)
%              Number of leaves         :   35 ( 258 expanded)
%              Depth                    :   24
%              Number of atoms          : 1322 (5839 expanded)
%              Number of equality atoms :  131 ( 675 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X72: $i,X73: $i] :
      ( ( ( k4_xboole_0 @ X72 @ ( k1_tarski @ X73 ) )
        = X72 )
      | ( r2_hidden @ X73 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ! [X72: $i,X73: $i] :
      ( ( ( k4_xboole_0 @ X72 @ ( k1_tarski @ X73 ) )
        = X72 )
      | ( r2_hidden @ X73 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X68: $i,X70: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X68 ) @ X70 )
      | ~ ( r2_hidden @ X68 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_tarski @ X1 @ X1 ) )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','46'])).

thf(t141_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( r2_hidden @ A @ B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t141_zfmisc_1])).

thf('48',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
     != sk_B )
    | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B != sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('63',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('65',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X22 @ X23 ) @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('71',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('72',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X33 @ X37 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('73',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) )
      | ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X28 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('79',plain,(
    ! [X72: $i,X73: $i] :
      ( ( ( k4_xboole_0 @ X72 @ ( k1_tarski @ X73 ) )
        = X72 )
      | ( r2_hidden @ X73 @ X72 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('80',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ X27 )
      = ( k5_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ ( k5_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('92',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r2_hidden @ X71 @ X72 )
      | ( ( k4_xboole_0 @ X72 @ ( k1_tarski @ X71 ) )
       != X72 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
       != ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['90','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['78','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','103'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('105',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('106',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','106'])).

thf('108',plain,(
    ! [X68: $i,X70: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X68 ) @ X70 )
      | ~ ( r2_hidden @ X68 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','111'])).

thf('113',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('114',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('116',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','119'])).

thf('121',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('122',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('123',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('126',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['120','126'])).

thf('128',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['127','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cSm7jJZbPa
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:03:27 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 2.19/2.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.19/2.39  % Solved by: fo/fo7.sh
% 2.19/2.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.19/2.39  % done 2530 iterations in 1.931s
% 2.19/2.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.19/2.39  % SZS output start Refutation
% 2.19/2.39  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.19/2.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.19/2.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.19/2.39  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.19/2.39  thf(sk_A_type, type, sk_A: $i).
% 2.19/2.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.19/2.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.19/2.39  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.19/2.39  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.19/2.39  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.19/2.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.19/2.39  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.19/2.39  thf(sk_B_type, type, sk_B: $i).
% 2.19/2.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.19/2.39  thf(t65_zfmisc_1, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.19/2.39       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.19/2.39  thf('0', plain,
% 2.19/2.39      (![X72 : $i, X73 : $i]:
% 2.19/2.39         (((k4_xboole_0 @ X72 @ (k1_tarski @ X73)) = (X72))
% 2.19/2.39          | (r2_hidden @ X73 @ X72))),
% 2.19/2.39      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.19/2.39  thf(t69_enumset1, axiom,
% 2.19/2.39    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.19/2.39  thf('1', plain, (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 2.19/2.39      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.19/2.39  thf('2', plain, (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 2.19/2.39      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.19/2.39  thf('3', plain,
% 2.19/2.39      (![X72 : $i, X73 : $i]:
% 2.19/2.39         (((k4_xboole_0 @ X72 @ (k1_tarski @ X73)) = (X72))
% 2.19/2.39          | (r2_hidden @ X73 @ X72))),
% 2.19/2.39      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.19/2.39  thf(t79_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.19/2.39  thf('4', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 2.19/2.39      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.19/2.39  thf('5', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['3', '4'])).
% 2.19/2.39  thf('6', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((r1_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) | (r2_hidden @ X0 @ X1))),
% 2.19/2.39      inference('sup+', [status(thm)], ['2', '5'])).
% 2.19/2.39  thf(l1_zfmisc_1, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 2.19/2.39  thf('7', plain,
% 2.19/2.39      (![X68 : $i, X70 : $i]:
% 2.19/2.39         ((r1_tarski @ (k1_tarski @ X68) @ X70) | ~ (r2_hidden @ X68 @ X70))),
% 2.19/2.39      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.19/2.39  thf('8', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((r1_xboole_0 @ X0 @ (k2_tarski @ X1 @ X1))
% 2.19/2.39          | (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 2.19/2.39      inference('sup-', [status(thm)], ['6', '7'])).
% 2.19/2.39  thf('9', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 2.19/2.39          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 2.19/2.39      inference('sup+', [status(thm)], ['1', '8'])).
% 2.19/2.39  thf(t28_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.19/2.39  thf('10', plain,
% 2.19/2.39      (![X13 : $i, X14 : $i]:
% 2.19/2.39         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 2.19/2.39      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.19/2.39  thf('11', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1))
% 2.19/2.39          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 2.19/2.39      inference('sup-', [status(thm)], ['9', '10'])).
% 2.19/2.39  thf(commutativity_k5_xboole_0, axiom,
% 2.19/2.39    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 2.19/2.39  thf('12', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf(t94_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( k2_xboole_0 @ A @ B ) =
% 2.19/2.39       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.19/2.39  thf('13', plain,
% 2.19/2.39      (![X22 : $i, X23 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X22 @ X23)
% 2.19/2.39           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 2.19/2.39              (k3_xboole_0 @ X22 @ X23)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t94_xboole_1])).
% 2.19/2.39  thf('14', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf('15', plain,
% 2.19/2.39      (![X22 : $i, X23 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X22 @ X23)
% 2.19/2.39           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 2.19/2.39              (k5_xboole_0 @ X22 @ X23)))),
% 2.19/2.39      inference('demod', [status(thm)], ['13', '14'])).
% 2.19/2.39  thf('16', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X0 @ X1)
% 2.19/2.39           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['12', '15'])).
% 2.19/2.39  thf('17', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf(t92_xboole_1, axiom,
% 2.19/2.39    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 2.19/2.39  thf('18', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 2.19/2.39      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.19/2.39  thf(t91_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i,C:$i]:
% 2.19/2.39     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 2.19/2.39       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 2.19/2.39  thf('19', plain,
% 2.19/2.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.19/2.39         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 2.19/2.39           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.19/2.39  thf('20', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 2.19/2.39           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['18', '19'])).
% 2.19/2.39  thf('21', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf(t5_boole, axiom,
% 2.19/2.39    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.19/2.39  thf('22', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 2.19/2.39      inference('cnf', [status(esa)], [t5_boole])).
% 2.19/2.39  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['21', '22'])).
% 2.19/2.39  thf('24', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['20', '23'])).
% 2.19/2.39  thf('25', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['17', '24'])).
% 2.19/2.39  thf('26', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X1 @ X0)
% 2.19/2.39           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['16', '25'])).
% 2.19/2.39  thf('27', plain,
% 2.19/2.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.19/2.39         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 2.19/2.39           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.19/2.39  thf(t98_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 2.19/2.39  thf('28', plain,
% 2.19/2.39      (![X26 : $i, X27 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X26 @ X27)
% 2.19/2.39           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.19/2.39  thf('29', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['20', '23'])).
% 2.19/2.39  thf('30', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X0 @ X1)
% 2.19/2.39           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['28', '29'])).
% 2.19/2.39  thf('31', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X1 @ X0)
% 2.19/2.39           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.19/2.39      inference('demod', [status(thm)], ['26', '27', '30'])).
% 2.19/2.39  thf('32', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['17', '24'])).
% 2.19/2.39  thf('33', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X0)
% 2.19/2.39           = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['31', '32'])).
% 2.19/2.39  thf('34', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf('35', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X0)
% 2.19/2.39           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 2.19/2.39      inference('demod', [status(thm)], ['33', '34'])).
% 2.19/2.39  thf('36', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (((X1)
% 2.19/2.39            = (k5_xboole_0 @ (k1_tarski @ X0) @ 
% 2.19/2.39               (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))
% 2.19/2.39          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['11', '35'])).
% 2.19/2.39  thf('37', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf(t95_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( k3_xboole_0 @ A @ B ) =
% 2.19/2.39       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 2.19/2.39  thf('38', plain,
% 2.19/2.39      (![X24 : $i, X25 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X24 @ X25)
% 2.19/2.39           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 2.19/2.39              (k2_xboole_0 @ X24 @ X25)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t95_xboole_1])).
% 2.19/2.39  thf('39', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf('40', plain,
% 2.19/2.39      (![X24 : $i, X25 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X24 @ X25)
% 2.19/2.39           = (k5_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ 
% 2.19/2.39              (k5_xboole_0 @ X24 @ X25)))),
% 2.19/2.39      inference('demod', [status(thm)], ['38', '39'])).
% 2.19/2.39  thf('41', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X0 @ X1)
% 2.19/2.39           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['37', '40'])).
% 2.19/2.39  thf('42', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['17', '24'])).
% 2.19/2.39  thf('43', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X1 @ X0)
% 2.19/2.39           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['41', '42'])).
% 2.19/2.39  thf('44', plain,
% 2.19/2.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.19/2.39         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 2.19/2.39           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t91_xboole_1])).
% 2.19/2.39  thf(t100_xboole_1, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.19/2.39  thf('45', plain,
% 2.19/2.39      (![X11 : $i, X12 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X11 @ X12)
% 2.19/2.39           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.19/2.39  thf('46', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X1 @ X0)
% 2.19/2.39           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['43', '44', '45'])).
% 2.19/2.39  thf('47', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (((X1) = (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.19/2.39          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['36', '46'])).
% 2.19/2.39  thf(t141_zfmisc_1, conjecture,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( ~( r2_hidden @ A @ B ) ) =>
% 2.19/2.39       ( ( k4_xboole_0 @
% 2.19/2.39           ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 2.19/2.39         ( B ) ) ))).
% 2.19/2.39  thf(zf_stmt_0, negated_conjecture,
% 2.19/2.39    (~( ![A:$i,B:$i]:
% 2.19/2.39        ( ( ~( r2_hidden @ A @ B ) ) =>
% 2.19/2.39          ( ( k4_xboole_0 @
% 2.19/2.39              ( k2_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 2.19/2.39            ( B ) ) ) )),
% 2.19/2.39    inference('cnf.neg', [status(esa)], [t141_zfmisc_1])).
% 2.19/2.39  thf('48', plain,
% 2.19/2.39      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 2.19/2.39         (k1_tarski @ sk_A)) != (sk_B))),
% 2.19/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.39  thf('49', plain,
% 2.19/2.39      ((((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))
% 2.19/2.39        | (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.19/2.39      inference('sup-', [status(thm)], ['47', '48'])).
% 2.19/2.39  thf('50', plain,
% 2.19/2.39      ((((sk_B) != (sk_B))
% 2.19/2.39        | (r2_hidden @ sk_A @ sk_B)
% 2.19/2.39        | (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.19/2.39      inference('sup-', [status(thm)], ['0', '49'])).
% 2.19/2.39  thf('51', plain,
% 2.19/2.39      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 2.19/2.39      inference('simplify', [status(thm)], ['50'])).
% 2.19/2.39  thf('52', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 2.19/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.39  thf('53', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A))),
% 2.19/2.39      inference('clc', [status(thm)], ['51', '52'])).
% 2.19/2.39  thf(d7_xboole_0, axiom,
% 2.19/2.39    (![A:$i,B:$i]:
% 2.19/2.39     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.19/2.39       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.19/2.39  thf('54', plain,
% 2.19/2.39      (![X8 : $i, X9 : $i]:
% 2.19/2.39         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 2.19/2.39      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.19/2.39  thf('55', plain,
% 2.19/2.39      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 2.19/2.39      inference('sup-', [status(thm)], ['53', '54'])).
% 2.19/2.39  thf('56', plain,
% 2.19/2.39      (![X24 : $i, X25 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X24 @ X25)
% 2.19/2.39           = (k5_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ 
% 2.19/2.39              (k5_xboole_0 @ X24 @ X25)))),
% 2.19/2.39      inference('demod', [status(thm)], ['38', '39'])).
% 2.19/2.39  thf('57', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['20', '23'])).
% 2.19/2.39  thf('58', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k5_xboole_0 @ X1 @ X0)
% 2.19/2.39           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['56', '57'])).
% 2.19/2.39  thf('59', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf('60', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k5_xboole_0 @ X1 @ X0)
% 2.19/2.39           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['58', '59'])).
% 2.19/2.39  thf('61', plain,
% 2.19/2.39      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 2.19/2.39         = (k5_xboole_0 @ k1_xboole_0 @ 
% 2.19/2.39            (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 2.19/2.39      inference('sup+', [status(thm)], ['55', '60'])).
% 2.19/2.39  thf('62', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['21', '22'])).
% 2.19/2.39  thf('63', plain,
% 2.19/2.39      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 2.19/2.39         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.19/2.39      inference('demod', [status(thm)], ['61', '62'])).
% 2.19/2.39  thf('64', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['17', '24'])).
% 2.19/2.39  thf('65', plain,
% 2.19/2.39      (![X22 : $i, X23 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X22 @ X23)
% 2.19/2.39           = (k5_xboole_0 @ (k3_xboole_0 @ X22 @ X23) @ 
% 2.19/2.39              (k5_xboole_0 @ X22 @ X23)))),
% 2.19/2.39      inference('demod', [status(thm)], ['13', '14'])).
% 2.19/2.39  thf('66', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1))
% 2.19/2.39           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1)) @ X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['64', '65'])).
% 2.19/2.39  thf('67', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf('68', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1))
% 2.19/2.39           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X1))))),
% 2.19/2.39      inference('demod', [status(thm)], ['66', '67'])).
% 2.19/2.39  thf('69', plain,
% 2.19/2.39      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.19/2.39         (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 2.19/2.39         = (k5_xboole_0 @ sk_B @ 
% 2.19/2.39            (k3_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.19/2.39             (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))))),
% 2.19/2.39      inference('sup+', [status(thm)], ['63', '68'])).
% 2.19/2.39  thf('70', plain,
% 2.19/2.39      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 2.19/2.39         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.19/2.39      inference('demod', [status(thm)], ['61', '62'])).
% 2.19/2.39  thf(t70_enumset1, axiom,
% 2.19/2.39    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.19/2.39  thf('71', plain,
% 2.19/2.39      (![X41 : $i, X42 : $i]:
% 2.19/2.39         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 2.19/2.39      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.19/2.39  thf(d1_enumset1, axiom,
% 2.19/2.39    (![A:$i,B:$i,C:$i,D:$i]:
% 2.19/2.39     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.19/2.39       ( ![E:$i]:
% 2.19/2.39         ( ( r2_hidden @ E @ D ) <=>
% 2.19/2.39           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.19/2.39  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.19/2.39  thf(zf_stmt_2, axiom,
% 2.19/2.39    (![E:$i,C:$i,B:$i,A:$i]:
% 2.19/2.39     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.19/2.39       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.19/2.39  thf(zf_stmt_3, axiom,
% 2.19/2.39    (![A:$i,B:$i,C:$i,D:$i]:
% 2.19/2.39     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.19/2.39       ( ![E:$i]:
% 2.19/2.39         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.19/2.39  thf('72', plain,
% 2.19/2.39      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.19/2.39         ((zip_tseitin_0 @ X33 @ X34 @ X35 @ X36)
% 2.19/2.39          | (r2_hidden @ X33 @ X37)
% 2.19/2.39          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 2.19/2.39      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.19/2.39  thf('73', plain,
% 2.19/2.39      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.19/2.39         ((r2_hidden @ X33 @ (k1_enumset1 @ X36 @ X35 @ X34))
% 2.19/2.39          | (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36))),
% 2.19/2.39      inference('simplify', [status(thm)], ['72'])).
% 2.19/2.39  thf('74', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.39         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.19/2.39          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.19/2.39      inference('sup+', [status(thm)], ['71', '73'])).
% 2.19/2.39  thf('75', plain,
% 2.19/2.39      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.19/2.39         (((X29) != (X28)) | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X28))),
% 2.19/2.39      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.19/2.39  thf('76', plain,
% 2.19/2.39      (![X28 : $i, X30 : $i, X31 : $i]:
% 2.19/2.39         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X28)),
% 2.19/2.39      inference('simplify', [status(thm)], ['75'])).
% 2.19/2.39  thf('77', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.19/2.39      inference('sup-', [status(thm)], ['74', '76'])).
% 2.19/2.39  thf('78', plain,
% 2.19/2.39      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 2.19/2.39      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.19/2.39  thf('79', plain,
% 2.19/2.39      (![X72 : $i, X73 : $i]:
% 2.19/2.39         (((k4_xboole_0 @ X72 @ (k1_tarski @ X73)) = (X72))
% 2.19/2.39          | (r2_hidden @ X73 @ X72))),
% 2.19/2.39      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.19/2.39  thf('80', plain,
% 2.19/2.39      (![X26 : $i, X27 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X26 @ X27)
% 2.19/2.39           = (k5_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t98_xboole_1])).
% 2.19/2.39  thf('81', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (((k2_xboole_0 @ (k1_tarski @ X1) @ X0)
% 2.19/2.39            = (k5_xboole_0 @ (k1_tarski @ X1) @ X0))
% 2.19/2.39          | (r2_hidden @ X1 @ X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['79', '80'])).
% 2.19/2.39  thf('82', plain,
% 2.19/2.39      (![X24 : $i, X25 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ X24 @ X25)
% 2.19/2.39           = (k5_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ 
% 2.19/2.39              (k5_xboole_0 @ X24 @ X25)))),
% 2.19/2.39      inference('demod', [status(thm)], ['38', '39'])).
% 2.19/2.39  thf('83', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0)
% 2.19/2.39            = (k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ 
% 2.19/2.39               (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))
% 2.19/2.39          | (r2_hidden @ X1 @ X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['81', '82'])).
% 2.19/2.39  thf('84', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 2.19/2.39      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.19/2.39  thf('85', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 2.19/2.39          | (r2_hidden @ X1 @ X0))),
% 2.19/2.39      inference('demod', [status(thm)], ['83', '84'])).
% 2.19/2.39  thf('86', plain,
% 2.19/2.39      (![X11 : $i, X12 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X11 @ X12)
% 2.19/2.39           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.19/2.39  thf('87', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 2.19/2.39            = (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 2.19/2.39          | (r2_hidden @ X1 @ X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['85', '86'])).
% 2.19/2.39  thf('88', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf('89', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['21', '22'])).
% 2.19/2.39  thf('90', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 2.19/2.39          | (r2_hidden @ X1 @ X0))),
% 2.19/2.39      inference('demod', [status(thm)], ['87', '88', '89'])).
% 2.19/2.39  thf('91', plain,
% 2.19/2.39      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 2.19/2.39      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.19/2.39  thf('92', plain,
% 2.19/2.39      (![X8 : $i, X9 : $i]:
% 2.19/2.39         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 2.19/2.39      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.19/2.39  thf('93', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 2.19/2.39      inference('sup-', [status(thm)], ['91', '92'])).
% 2.19/2.39  thf('94', plain,
% 2.19/2.39      (![X11 : $i, X12 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X11 @ X12)
% 2.19/2.39           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.19/2.39  thf('95', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 2.19/2.39           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['93', '94'])).
% 2.19/2.39  thf('96', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf('97', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['21', '22'])).
% 2.19/2.39  thf('98', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 2.19/2.39           = (k4_xboole_0 @ X1 @ X0))),
% 2.19/2.39      inference('demod', [status(thm)], ['95', '96', '97'])).
% 2.19/2.39  thf('99', plain,
% 2.19/2.39      (![X71 : $i, X72 : $i]:
% 2.19/2.39         (~ (r2_hidden @ X71 @ X72)
% 2.19/2.39          | ((k4_xboole_0 @ X72 @ (k1_tarski @ X71)) != (X72)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.19/2.39  thf('100', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 2.19/2.39            != (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.19/2.39          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 2.19/2.39      inference('sup-', [status(thm)], ['98', '99'])).
% 2.19/2.39  thf('101', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.19/2.39      inference('simplify', [status(thm)], ['100'])).
% 2.19/2.39  thf('102', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.19/2.39          | (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 2.19/2.39      inference('sup-', [status(thm)], ['90', '101'])).
% 2.19/2.39  thf('103', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 2.19/2.39          | (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 2.19/2.39      inference('sup-', [status(thm)], ['78', '102'])).
% 2.19/2.39  thf('104', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.19/2.39      inference('sup-', [status(thm)], ['77', '103'])).
% 2.19/2.39  thf(d3_xboole_0, axiom,
% 2.19/2.39    (![A:$i,B:$i,C:$i]:
% 2.19/2.39     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.19/2.39       ( ![D:$i]:
% 2.19/2.39         ( ( r2_hidden @ D @ C ) <=>
% 2.19/2.39           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.19/2.39  thf('105', plain,
% 2.19/2.39      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.19/2.39         (~ (r2_hidden @ X2 @ X3)
% 2.19/2.39          | (r2_hidden @ X2 @ X4)
% 2.19/2.39          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.19/2.39      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.19/2.39  thf('106', plain,
% 2.19/2.39      (![X2 : $i, X3 : $i, X5 : $i]:
% 2.19/2.39         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 2.19/2.39      inference('simplify', [status(thm)], ['105'])).
% 2.19/2.39  thf('107', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.19/2.39      inference('sup-', [status(thm)], ['104', '106'])).
% 2.19/2.39  thf('108', plain,
% 2.19/2.39      (![X68 : $i, X70 : $i]:
% 2.19/2.39         ((r1_tarski @ (k1_tarski @ X68) @ X70) | ~ (r2_hidden @ X68 @ X70))),
% 2.19/2.39      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.19/2.39  thf('109', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         (r1_tarski @ (k1_tarski @ X0) @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.19/2.39      inference('sup-', [status(thm)], ['107', '108'])).
% 2.19/2.39  thf('110', plain,
% 2.19/2.39      (![X13 : $i, X14 : $i]:
% 2.19/2.39         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 2.19/2.39      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.19/2.39  thf('111', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k3_xboole_0 @ (k1_tarski @ X0) @ 
% 2.19/2.39           (k2_xboole_0 @ X1 @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 2.19/2.39      inference('sup-', [status(thm)], ['109', '110'])).
% 2.19/2.39  thf('112', plain,
% 2.19/2.39      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.19/2.39         (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 2.19/2.39         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.19/2.39      inference('demod', [status(thm)], ['69', '70', '111'])).
% 2.19/2.39  thf('113', plain,
% 2.19/2.39      (((k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 2.19/2.39         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.19/2.39      inference('demod', [status(thm)], ['61', '62'])).
% 2.19/2.39  thf('114', plain,
% 2.19/2.39      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.19/2.39         (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 2.19/2.39         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.19/2.39      inference('demod', [status(thm)], ['112', '113'])).
% 2.19/2.39  thf('115', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X0 @ X1)
% 2.19/2.39           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['28', '29'])).
% 2.19/2.39  thf('116', plain,
% 2.19/2.39      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 2.19/2.39         (k1_tarski @ sk_A))
% 2.19/2.39         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.19/2.39            (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 2.19/2.39      inference('sup+', [status(thm)], ['114', '115'])).
% 2.19/2.39  thf('117', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k2_xboole_0 @ X1 @ X0)
% 2.19/2.39           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['43', '44', '45'])).
% 2.19/2.39  thf('118', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('demod', [status(thm)], ['20', '23'])).
% 2.19/2.39  thf('119', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X1 @ X0)
% 2.19/2.39           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.19/2.39      inference('sup+', [status(thm)], ['117', '118'])).
% 2.19/2.39  thf('120', plain,
% 2.19/2.39      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 2.19/2.39         (k1_tarski @ sk_A)) = (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.19/2.39      inference('demod', [status(thm)], ['116', '119'])).
% 2.19/2.39  thf('121', plain,
% 2.19/2.39      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 2.19/2.39      inference('sup-', [status(thm)], ['53', '54'])).
% 2.19/2.39  thf('122', plain,
% 2.19/2.39      (![X11 : $i, X12 : $i]:
% 2.19/2.39         ((k4_xboole_0 @ X11 @ X12)
% 2.19/2.39           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 2.19/2.39      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.19/2.39  thf('123', plain,
% 2.19/2.39      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 2.19/2.39         = (k5_xboole_0 @ sk_B @ k1_xboole_0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['121', '122'])).
% 2.19/2.39  thf('124', plain,
% 2.19/2.39      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 2.19/2.39      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.19/2.39  thf('125', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.19/2.39      inference('sup+', [status(thm)], ['21', '22'])).
% 2.19/2.39  thf('126', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 2.19/2.39      inference('demod', [status(thm)], ['123', '124', '125'])).
% 2.19/2.39  thf('127', plain,
% 2.19/2.39      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 2.19/2.39         (k1_tarski @ sk_A)) = (sk_B))),
% 2.19/2.39      inference('demod', [status(thm)], ['120', '126'])).
% 2.19/2.39  thf('128', plain,
% 2.19/2.39      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 2.19/2.39         (k1_tarski @ sk_A)) != (sk_B))),
% 2.19/2.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.39  thf('129', plain, ($false),
% 2.19/2.39      inference('simplify_reflect-', [status(thm)], ['127', '128'])).
% 2.19/2.39  
% 2.19/2.39  % SZS output end Refutation
% 2.19/2.39  
% 2.26/2.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
