%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DUmxO3kE8j

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:48 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 148 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  697 (1320 expanded)
%              Number of equality atoms :   66 ( 102 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('21',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','22'])).

thf('25',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X24 @ X25 @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('30',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('31',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('34',plain,(
    ! [X45: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('35',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X43 @ X44 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X43 ) @ ( k1_setfam_1 @ X44 ) ) )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X45: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X6: $i] :
      ( ( r1_xboole_0 @ X6 @ X6 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('46',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['44','53'])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','54'])).

thf('56',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('59',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference('sup-',[status(thm)],['23','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DUmxO3kE8j
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:33:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 477 iterations in 0.224s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.69  thf(t70_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      (![X34 : $i, X35 : $i]:
% 0.45/0.69         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.69  thf(d1_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.69       ( ![E:$i]:
% 0.45/0.69         ( ( r2_hidden @ E @ D ) <=>
% 0.45/0.69           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.69  thf(zf_stmt_1, axiom,
% 0.45/0.69    (![E:$i,C:$i,B:$i,A:$i]:
% 0.45/0.69     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.45/0.69       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_2, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.69       ( ![E:$i]:
% 0.45/0.69         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.45/0.69          | (r2_hidden @ X13 @ X17)
% 0.45/0.69          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.69         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.45/0.69          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.45/0.69      inference('simplify', [status(thm)], ['1'])).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.69          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['0', '2'])).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.69         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.45/0.69      inference('simplify', [status(thm)], ['4'])).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['3', '5'])).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.69         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.45/0.69          | ((X9) = (X10))
% 0.45/0.69          | ((X9) = (X11))
% 0.45/0.69          | ((X9) = (X12)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.69  thf(t3_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.45/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.69            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.69  thf(t69_enumset1, axiom,
% 0.45/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.69  thf('9', plain, (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.45/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      (![X34 : $i, X35 : $i]:
% 0.45/0.69         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X18 @ X17)
% 0.45/0.69          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.45/0.69          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.45/0.69         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.45/0.69          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.69          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['10', '12'])).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.45/0.69          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['9', '13'])).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.45/0.69          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['8', '14'])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.45/0.69          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.45/0.69          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.45/0.69          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['7', '15'])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.45/0.69          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['16'])).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.45/0.69          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.45/0.69          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['17', '18'])).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.45/0.69          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.69  thf(l24_zfmisc_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X39 : $i, X40 : $i]:
% 0.45/0.69         (~ (r1_xboole_0 @ (k1_tarski @ X39) @ X40) | ~ (r2_hidden @ X39 @ X40))),
% 0.45/0.69      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r2_hidden @ X1 @ (k1_tarski @ X1)) | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.69  thf('23', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['6', '22'])).
% 0.45/0.69  thf('24', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['6', '22'])).
% 0.45/0.69  thf('25', plain,
% 0.45/0.69      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.45/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      (![X34 : $i, X35 : $i]:
% 0.45/0.69         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.69  thf(t46_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.45/0.69       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.69         ((k2_enumset1 @ X24 @ X25 @ X26 @ X27)
% 0.45/0.69           = (k2_xboole_0 @ (k1_enumset1 @ X24 @ X25 @ X26) @ (k1_tarski @ X27)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.45/0.69           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.45/0.69           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['25', '28'])).
% 0.45/0.69  thf(t71_enumset1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.69  thf('30', plain,
% 0.45/0.69      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.69         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.45/0.69           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.45/0.69      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.69  thf('31', plain,
% 0.45/0.69      (![X34 : $i, X35 : $i]:
% 0.45/0.69         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.45/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['30', '31'])).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k2_tarski @ X0 @ X1)
% 0.45/0.69           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.69      inference('demod', [status(thm)], ['29', '32'])).
% 0.45/0.69  thf(t11_setfam_1, axiom,
% 0.45/0.69    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.45/0.69  thf('34', plain, (![X45 : $i]: ((k1_setfam_1 @ (k1_tarski @ X45)) = (X45))),
% 0.45/0.69      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.69  thf(t10_setfam_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.69          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.45/0.69            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.45/0.69  thf('35', plain,
% 0.45/0.69      (![X43 : $i, X44 : $i]:
% 0.45/0.69         (((X43) = (k1_xboole_0))
% 0.45/0.69          | ((k1_setfam_1 @ (k2_xboole_0 @ X43 @ X44))
% 0.45/0.69              = (k3_xboole_0 @ (k1_setfam_1 @ X43) @ (k1_setfam_1 @ X44)))
% 0.45/0.69          | ((X44) = (k1_xboole_0)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.45/0.69            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.45/0.69          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.45/0.69          | ((X1) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['34', '35'])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.45/0.69            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.45/0.69          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.45/0.69          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['33', '36'])).
% 0.45/0.69  thf('38', plain, (![X45 : $i]: ((k1_setfam_1 @ (k1_tarski @ X45)) = (X45))),
% 0.45/0.69      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.45/0.69          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.45/0.69          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.69  thf(t12_setfam_1, conjecture,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.69  thf(zf_stmt_3, negated_conjecture,
% 0.45/0.69    (~( ![A:$i,B:$i]:
% 0.45/0.69        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.45/0.69  thf('40', plain,
% 0.45/0.69      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.45/0.69         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.45/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.45/0.69        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.69  thf('42', plain,
% 0.45/0.69      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.69        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['41'])).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      (![X39 : $i, X40 : $i]:
% 0.45/0.69         (~ (r1_xboole_0 @ (k1_tarski @ X39) @ X40) | ~ (r2_hidden @ X39 @ X40))),
% 0.45/0.69      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.69          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.69          | ~ (r2_hidden @ sk_B @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.69  thf(t66_xboole_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.45/0.69       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.45/0.69  thf('45', plain,
% 0.45/0.69      (![X6 : $i]: ((r1_xboole_0 @ X6 @ X6) | ((X6) != (k1_xboole_0)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.45/0.69  thf('46', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.69      inference('simplify', [status(thm)], ['45'])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X2 @ X0)
% 0.45/0.69          | ~ (r2_hidden @ X2 @ X3)
% 0.45/0.69          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.69  thf('50', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X0 @ X1)
% 0.45/0.69          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.45/0.69          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.69  thf('51', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X0 @ X1)
% 0.45/0.69          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.45/0.69          | (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['47', '50'])).
% 0.45/0.69  thf('52', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('simplify', [status(thm)], ['51'])).
% 0.45/0.69  thf('53', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.69      inference('sup-', [status(thm)], ['46', '52'])).
% 0.45/0.69  thf('54', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k1_tarski @ sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ sk_B @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['44', '53'])).
% 0.45/0.69  thf('55', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['24', '54'])).
% 0.45/0.69  thf('56', plain,
% 0.45/0.69      (![X39 : $i, X40 : $i]:
% 0.45/0.69         (~ (r1_xboole_0 @ (k1_tarski @ X39) @ X40) | ~ (r2_hidden @ X39 @ X40))),
% 0.45/0.69      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.45/0.69  thf('57', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.69  thf('58', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.69      inference('sup-', [status(thm)], ['46', '52'])).
% 0.45/0.69  thf('59', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.45/0.69      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.69  thf('60', plain, ($false), inference('sup-', [status(thm)], ['23', '59'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
