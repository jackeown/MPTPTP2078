%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1UEkUE5KVK

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:38 EST 2020

% Result     : Theorem 0.96s
% Output     : Refutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 138 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :   21
%              Number of atoms          :  672 (1118 expanded)
%              Number of equality atoms :   97 ( 178 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X73: $i,X75: $i,X76: $i] :
      ( ( r1_tarski @ X75 @ ( k2_tarski @ X73 @ X76 ) )
      | ( X75
       != ( k1_tarski @ X73 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('2',plain,(
    ! [X73: $i,X76: $i] :
      ( r1_tarski @ ( k1_tarski @ X73 ) @ ( k2_tarski @ X73 @ X76 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X73: $i,X74: $i,X75: $i] :
      ( ( X75
        = ( k2_tarski @ X73 @ X74 ) )
      | ( X75
        = ( k1_tarski @ X74 ) )
      | ( X75
        = ( k1_tarski @ X73 ) )
      | ( X75 = k1_xboole_0 )
      | ~ ( r1_tarski @ X75 @ ( k2_tarski @ X73 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('13',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X31 != X30 )
      | ( r2_hidden @ X31 @ X32 )
      | ( X32
       != ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('14',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X30 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X45: $i] :
      ( ( k2_tarski @ X45 @ X45 )
      = ( k1_tarski @ X45 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X30: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X32 )
      | ( X34 = X33 )
      | ( X34 = X30 )
      | ( X32
       != ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X30: $i,X33: $i,X34: $i] :
      ( ( X34 = X30 )
      | ( X34 = X33 )
      | ~ ( r2_hidden @ X34 @ ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_A ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X45: $i] :
      ( ( k2_tarski @ X45 @ X45 )
      = ( k1_tarski @ X45 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X30 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('33',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('38',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( k2_enumset1 @ X48 @ X48 @ X49 @ X50 )
      = ( k1_enumset1 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_enumset1 @ X46 @ X46 @ X47 )
      = ( k2_tarski @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('42',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X36 @ X37 @ X38 ) @ ( k1_tarski @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X45: $i] :
      ( ( k2_tarski @ X45 @ X45 )
      = ( k1_tarski @ X45 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ sk_A )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('49',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('53',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ sk_A )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['47','58'])).

thf('60',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X30 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('63',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1UEkUE5KVK
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.96/1.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.96/1.15  % Solved by: fo/fo7.sh
% 0.96/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.96/1.15  % done 2176 iterations in 0.699s
% 0.96/1.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.96/1.15  % SZS output start Refutation
% 0.96/1.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.96/1.15  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.96/1.15  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.96/1.15  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.96/1.15  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.96/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.96/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.96/1.15  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.96/1.15  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.96/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.96/1.15  thf(sk_C_type, type, sk_C: $i).
% 0.96/1.15  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.96/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.96/1.15  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.96/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.96/1.15  thf(t28_zfmisc_1, conjecture,
% 0.96/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.96/1.15     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.96/1.15          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.96/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.96/1.15    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.96/1.15        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.96/1.15             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.96/1.15    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.96/1.15  thf('0', plain, (((sk_A) != (sk_D_1))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(l45_zfmisc_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.96/1.15       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.96/1.15            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.96/1.15  thf('1', plain,
% 0.96/1.15      (![X73 : $i, X75 : $i, X76 : $i]:
% 0.96/1.15         ((r1_tarski @ X75 @ (k2_tarski @ X73 @ X76))
% 0.96/1.15          | ((X75) != (k1_tarski @ X73)))),
% 0.96/1.15      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.96/1.15  thf('2', plain,
% 0.96/1.15      (![X73 : $i, X76 : $i]:
% 0.96/1.15         (r1_tarski @ (k1_tarski @ X73) @ (k2_tarski @ X73 @ X76))),
% 0.96/1.15      inference('simplify', [status(thm)], ['1'])).
% 0.96/1.15  thf('3', plain,
% 0.96/1.15      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf(t28_xboole_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.96/1.15  thf('4', plain,
% 0.96/1.15      (![X10 : $i, X11 : $i]:
% 0.96/1.15         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.96/1.15      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.96/1.15  thf('5', plain,
% 0.96/1.15      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.96/1.15         = (k2_tarski @ sk_A @ sk_B))),
% 0.96/1.15      inference('sup-', [status(thm)], ['3', '4'])).
% 0.96/1.15  thf(commutativity_k3_xboole_0, axiom,
% 0.96/1.15    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.96/1.15  thf('6', plain,
% 0.96/1.15      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.96/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.96/1.15  thf(t18_xboole_1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.96/1.15  thf('7', plain,
% 0.96/1.15      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.96/1.15         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.96/1.15      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.96/1.15  thf('8', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.15         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.96/1.15      inference('sup-', [status(thm)], ['6', '7'])).
% 0.96/1.15  thf('9', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.96/1.15          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['5', '8'])).
% 0.96/1.15  thf('10', plain,
% 0.96/1.15      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.96/1.15      inference('sup-', [status(thm)], ['2', '9'])).
% 0.96/1.15  thf('11', plain,
% 0.96/1.15      (![X73 : $i, X74 : $i, X75 : $i]:
% 0.96/1.15         (((X75) = (k2_tarski @ X73 @ X74))
% 0.96/1.15          | ((X75) = (k1_tarski @ X74))
% 0.96/1.15          | ((X75) = (k1_tarski @ X73))
% 0.96/1.15          | ((X75) = (k1_xboole_0))
% 0.96/1.15          | ~ (r1_tarski @ X75 @ (k2_tarski @ X73 @ X74)))),
% 0.96/1.15      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.96/1.15  thf('12', plain,
% 0.96/1.15      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D_1))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k2_tarski @ sk_C @ sk_D_1)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['10', '11'])).
% 0.96/1.15  thf(d2_tarski, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.96/1.15       ( ![D:$i]:
% 0.96/1.15         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.96/1.15  thf('13', plain,
% 0.96/1.15      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.96/1.15         (((X31) != (X30))
% 0.96/1.15          | (r2_hidden @ X31 @ X32)
% 0.96/1.15          | ((X32) != (k2_tarski @ X33 @ X30)))),
% 0.96/1.15      inference('cnf', [status(esa)], [d2_tarski])).
% 0.96/1.15  thf('14', plain,
% 0.96/1.15      (![X30 : $i, X33 : $i]: (r2_hidden @ X30 @ (k2_tarski @ X33 @ X30))),
% 0.96/1.15      inference('simplify', [status(thm)], ['13'])).
% 0.96/1.15  thf('15', plain,
% 0.96/1.15      (((r2_hidden @ sk_D_1 @ (k1_tarski @ sk_A))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D_1))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.96/1.15      inference('sup+', [status(thm)], ['12', '14'])).
% 0.96/1.15  thf(t69_enumset1, axiom,
% 0.96/1.15    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.96/1.15  thf('16', plain,
% 0.96/1.15      (![X45 : $i]: ((k2_tarski @ X45 @ X45) = (k1_tarski @ X45))),
% 0.96/1.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.96/1.15  thf('17', plain,
% 0.96/1.15      (![X30 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.96/1.15         (~ (r2_hidden @ X34 @ X32)
% 0.96/1.15          | ((X34) = (X33))
% 0.96/1.15          | ((X34) = (X30))
% 0.96/1.15          | ((X32) != (k2_tarski @ X33 @ X30)))),
% 0.96/1.15      inference('cnf', [status(esa)], [d2_tarski])).
% 0.96/1.15  thf('18', plain,
% 0.96/1.15      (![X30 : $i, X33 : $i, X34 : $i]:
% 0.96/1.15         (((X34) = (X30))
% 0.96/1.15          | ((X34) = (X33))
% 0.96/1.15          | ~ (r2_hidden @ X34 @ (k2_tarski @ X33 @ X30)))),
% 0.96/1.15      inference('simplify', [status(thm)], ['17'])).
% 0.96/1.15  thf('19', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]:
% 0.96/1.15         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['16', '18'])).
% 0.96/1.15  thf('20', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]:
% 0.96/1.15         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.96/1.15      inference('simplify', [status(thm)], ['19'])).
% 0.96/1.15  thf('21', plain,
% 0.96/1.15      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D_1))
% 0.96/1.15        | ((sk_D_1) = (sk_A)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['15', '20'])).
% 0.96/1.15  thf('22', plain, (((sk_A) != (sk_D_1))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('23', plain,
% 0.96/1.15      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D_1)))),
% 0.96/1.15      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.96/1.15  thf('24', plain,
% 0.96/1.15      (![X45 : $i]: ((k2_tarski @ X45 @ X45) = (k1_tarski @ X45))),
% 0.96/1.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.96/1.15  thf('25', plain,
% 0.96/1.15      (![X30 : $i, X33 : $i]: (r2_hidden @ X30 @ (k2_tarski @ X33 @ X30))),
% 0.96/1.15      inference('simplify', [status(thm)], ['13'])).
% 0.96/1.15  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.96/1.15      inference('sup+', [status(thm)], ['24', '25'])).
% 0.96/1.15  thf('27', plain,
% 0.96/1.15      (((r2_hidden @ sk_D_1 @ (k1_tarski @ sk_A))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.96/1.15      inference('sup+', [status(thm)], ['23', '26'])).
% 0.96/1.15  thf('28', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]:
% 0.96/1.15         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.96/1.15      inference('simplify', [status(thm)], ['19'])).
% 0.96/1.15  thf('29', plain,
% 0.96/1.15      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 0.96/1.15        | ((sk_D_1) = (sk_A)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['27', '28'])).
% 0.96/1.15  thf('30', plain, (((sk_A) != (sk_D_1))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('31', plain,
% 0.96/1.15      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C)))),
% 0.96/1.15      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.96/1.15  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.96/1.15      inference('sup+', [status(thm)], ['24', '25'])).
% 0.96/1.15  thf('33', plain,
% 0.96/1.15      (((r2_hidden @ sk_C @ (k1_tarski @ sk_A))
% 0.96/1.15        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.96/1.15      inference('sup+', [status(thm)], ['31', '32'])).
% 0.96/1.15  thf('34', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]:
% 0.96/1.15         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.96/1.15      inference('simplify', [status(thm)], ['19'])).
% 0.96/1.15  thf('35', plain,
% 0.96/1.15      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_A)))),
% 0.96/1.15      inference('sup-', [status(thm)], ['33', '34'])).
% 0.96/1.15  thf('36', plain, (((sk_A) != (sk_C))),
% 0.96/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.96/1.15  thf('37', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.96/1.15      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.96/1.15  thf(t71_enumset1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i]:
% 0.96/1.15     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.96/1.15  thf('38', plain,
% 0.96/1.15      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.96/1.15         ((k2_enumset1 @ X48 @ X48 @ X49 @ X50)
% 0.96/1.15           = (k1_enumset1 @ X48 @ X49 @ X50))),
% 0.96/1.15      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.96/1.15  thf(t70_enumset1, axiom,
% 0.96/1.15    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.96/1.15  thf('39', plain,
% 0.96/1.15      (![X46 : $i, X47 : $i]:
% 0.96/1.15         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 0.96/1.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.96/1.15  thf('40', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]:
% 0.96/1.15         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.96/1.15      inference('sup+', [status(thm)], ['38', '39'])).
% 0.96/1.15  thf('41', plain,
% 0.96/1.15      (![X46 : $i, X47 : $i]:
% 0.96/1.15         ((k1_enumset1 @ X46 @ X46 @ X47) = (k2_tarski @ X46 @ X47))),
% 0.96/1.15      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.96/1.15  thf(t46_enumset1, axiom,
% 0.96/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.96/1.15     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.96/1.15       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.96/1.15  thf('42', plain,
% 0.96/1.15      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.96/1.15         ((k2_enumset1 @ X36 @ X37 @ X38 @ X39)
% 0.96/1.15           = (k2_xboole_0 @ (k1_enumset1 @ X36 @ X37 @ X38) @ (k1_tarski @ X39)))),
% 0.96/1.15      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.96/1.15  thf('43', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.96/1.15         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.96/1.15           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.96/1.15      inference('sup+', [status(thm)], ['41', '42'])).
% 0.96/1.15  thf('44', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]:
% 0.96/1.15         ((k2_tarski @ X1 @ X0)
% 0.96/1.15           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.96/1.15      inference('sup+', [status(thm)], ['40', '43'])).
% 0.96/1.15  thf('45', plain,
% 0.96/1.15      (![X45 : $i]: ((k2_tarski @ X45 @ X45) = (k1_tarski @ X45))),
% 0.96/1.15      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.96/1.15  thf('46', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]:
% 0.96/1.15         ((k2_tarski @ X1 @ X0)
% 0.96/1.15           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.96/1.15      inference('demod', [status(thm)], ['44', '45'])).
% 0.96/1.15  thf('47', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((k2_tarski @ X0 @ sk_A)
% 0.96/1.15           = (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.96/1.15      inference('sup+', [status(thm)], ['37', '46'])).
% 0.96/1.15  thf('48', plain,
% 0.96/1.15      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.96/1.15      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.96/1.15  thf(t2_boole, axiom,
% 0.96/1.15    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.96/1.15  thf('49', plain,
% 0.96/1.15      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.96/1.15      inference('cnf', [status(esa)], [t2_boole])).
% 0.96/1.15  thf('50', plain,
% 0.96/1.15      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.96/1.15      inference('sup+', [status(thm)], ['48', '49'])).
% 0.96/1.15  thf(t100_xboole_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.96/1.15  thf('51', plain,
% 0.96/1.15      (![X5 : $i, X6 : $i]:
% 0.96/1.15         ((k4_xboole_0 @ X5 @ X6)
% 0.96/1.15           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.96/1.15      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.96/1.15  thf('52', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.96/1.15           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.96/1.15      inference('sup+', [status(thm)], ['50', '51'])).
% 0.96/1.15  thf(t5_boole, axiom,
% 0.96/1.15    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.96/1.15  thf('53', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.96/1.15      inference('cnf', [status(esa)], [t5_boole])).
% 0.96/1.15  thf('54', plain,
% 0.96/1.15      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.96/1.15      inference('demod', [status(thm)], ['52', '53'])).
% 0.96/1.15  thf(t98_xboole_1, axiom,
% 0.96/1.15    (![A:$i,B:$i]:
% 0.96/1.15     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.96/1.15  thf('55', plain,
% 0.96/1.15      (![X16 : $i, X17 : $i]:
% 0.96/1.15         ((k2_xboole_0 @ X16 @ X17)
% 0.96/1.15           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.96/1.15      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.96/1.15  thf('56', plain,
% 0.96/1.15      (![X0 : $i]:
% 0.96/1.15         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.96/1.15      inference('sup+', [status(thm)], ['54', '55'])).
% 0.96/1.15  thf('57', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.96/1.15      inference('cnf', [status(esa)], [t5_boole])).
% 0.96/1.15  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.96/1.15      inference('demod', [status(thm)], ['56', '57'])).
% 0.96/1.15  thf('59', plain, (![X0 : $i]: ((k2_tarski @ X0 @ sk_A) = (k1_tarski @ X0))),
% 0.96/1.15      inference('demod', [status(thm)], ['47', '58'])).
% 0.96/1.15  thf('60', plain,
% 0.96/1.15      (![X30 : $i, X33 : $i]: (r2_hidden @ X30 @ (k2_tarski @ X33 @ X30))),
% 0.96/1.15      inference('simplify', [status(thm)], ['13'])).
% 0.96/1.15  thf('61', plain, (![X0 : $i]: (r2_hidden @ sk_A @ (k1_tarski @ X0))),
% 0.96/1.15      inference('sup+', [status(thm)], ['59', '60'])).
% 0.96/1.15  thf('62', plain,
% 0.96/1.15      (![X0 : $i, X1 : $i]:
% 0.96/1.15         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.96/1.15      inference('simplify', [status(thm)], ['19'])).
% 0.96/1.15  thf('63', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.96/1.15      inference('sup-', [status(thm)], ['61', '62'])).
% 0.96/1.15  thf('64', plain, (((sk_A) != (sk_A))),
% 0.96/1.15      inference('demod', [status(thm)], ['0', '63'])).
% 0.96/1.15  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.96/1.15  
% 0.96/1.15  % SZS output end Refutation
% 0.96/1.15  
% 0.96/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
