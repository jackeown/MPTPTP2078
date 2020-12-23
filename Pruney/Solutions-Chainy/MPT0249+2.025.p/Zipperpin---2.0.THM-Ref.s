%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.btisQqDNEN

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:42 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 961 expanded)
%              Number of leaves         :   24 ( 289 expanded)
%              Depth                    :   19
%              Number of atoms          :  635 (7858 expanded)
%              Number of equality atoms :   82 (1077 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['17','38'])).

thf('40',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['17','38'])).

thf('46',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['17','38'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('47',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('51',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['49','56'])).

thf('58',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['46','57'])).

thf('59',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['45','58'])).

thf('60',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_B @ sk_C_2 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','61'])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) )
    | ( sk_C_2
      = ( k1_tarski @ ( sk_B @ sk_C_2 ) ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['45','58'])).

thf('70',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('72',plain,(
    r1_tarski @ sk_C_2 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['17','38'])).

thf('74',plain,(
    r1_tarski @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B @ sk_C_2 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','61'])).

thf('76',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['45','58'])).

thf('77',plain,
    ( ( sk_C_2 = sk_B_1 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69','74','75','76'])).

thf('78',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.btisQqDNEN
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 305 iterations in 0.123s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(t44_zfmisc_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.55          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.55        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.37/0.55             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.37/0.55  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t46_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X19 : $i, X20 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf(t39_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i]:
% 0.37/0.55         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.37/0.55           = (k2_xboole_0 @ X17 @ X18))),
% 0.37/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.37/0.55         = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.55  thf(t1_boole, axiom,
% 0.37/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.55  thf('6', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.37/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (((k1_tarski @ sk_A) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf(d3_tarski, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X1 : $i, X3 : $i]:
% 0.37/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.55  thf(d3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.55           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X5)
% 0.37/0.55          | (r2_hidden @ X4 @ X6)
% 0.37/0.55          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.37/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((r1_tarski @ X0 @ X1)
% 0.37/0.55          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['8', '10'])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X1 : $i, X3 : $i]:
% 0.37/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.37/0.55          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.55  thf('15', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['7', '14'])).
% 0.37/0.55  thf(d10_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X11 : $i, X13 : $i]:
% 0.37/0.55         (((X11) = (X13))
% 0.37/0.55          | ~ (r1_tarski @ X13 @ X11)
% 0.37/0.55          | ~ (r1_tarski @ X11 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.37/0.55        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (((k1_tarski @ sk_A) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf(t7_xboole_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X10 : $i]:
% 0.37/0.55         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.37/0.55      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((X0) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['18', '21'])).
% 0.37/0.55  thf('23', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('24', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_tarski @ sk_A))),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.37/0.55  thf(d1_tarski, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X24 @ X23)
% 0.37/0.55          | ((X24) = (X21))
% 0.37/0.55          | ((X23) != (k1_tarski @ X21)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_tarski])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      (![X21 : $i, X24 : $i]:
% 0.37/0.55         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.55  thf('27', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['24', '26'])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (![X10 : $i]:
% 0.37/0.55         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['27', '28'])).
% 0.37/0.55  thf('30', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('31', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (![X1 : $i, X3 : $i]:
% 0.37/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (![X21 : $i, X24 : $i]:
% 0.37/0.55         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.37/0.55          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      (![X1 : $i, X3 : $i]:
% 0.37/0.55         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.37/0.55          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.37/0.55          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.37/0.55  thf('38', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.37/0.55      inference('sup-', [status(thm)], ['31', '37'])).
% 0.37/0.55  thf('39', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['17', '38'])).
% 0.37/0.55  thf('40', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.37/0.55      inference('demod', [status(thm)], ['0', '39'])).
% 0.37/0.55  thf('41', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (((X0) = (k1_xboole_0))
% 0.37/0.55          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1) | ((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['40', '41'])).
% 0.37/0.55  thf('43', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('44', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.37/0.55  thf('45', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['17', '38'])).
% 0.37/0.55  thf('46', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['17', '38'])).
% 0.37/0.55  thf(t69_enumset1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.55  thf('47', plain,
% 0.37/0.55      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf(l51_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('48', plain,
% 0.37/0.55      (![X36 : $i, X37 : $i]:
% 0.37/0.55         ((k3_tarski @ (k2_tarski @ X36 @ X37)) = (k2_xboole_0 @ X36 @ X37))),
% 0.37/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.37/0.55  thf('49', plain,
% 0.37/0.55      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['47', '48'])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i]:
% 0.37/0.55         ((k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17))
% 0.37/0.55           = (k2_xboole_0 @ X17 @ X18))),
% 0.37/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.55  thf('51', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.37/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.55  thf('52', plain,
% 0.37/0.55      (![X19 : $i, X20 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.37/0.55  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['51', '52'])).
% 0.37/0.55  thf('54', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.37/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.55  thf('55', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((k2_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['53', '54'])).
% 0.37/0.55  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['50', '55'])).
% 0.37/0.55  thf('57', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['49', '56'])).
% 0.37/0.55  thf('58', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['46', '57'])).
% 0.37/0.55  thf('59', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['45', '58'])).
% 0.37/0.55  thf('60', plain,
% 0.37/0.55      (![X21 : $i, X24 : $i]:
% 0.37/0.55         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.55  thf('61', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (k3_tarski @ sk_B_1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.55  thf('62', plain, (((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['44', '61'])).
% 0.37/0.55  thf('63', plain,
% 0.37/0.55      (![X10 : $i]:
% 0.37/0.55         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.37/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.55  thf('64', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.37/0.55  thf('65', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.37/0.55  thf('66', plain,
% 0.37/0.55      (![X11 : $i, X13 : $i]:
% 0.37/0.55         (((X11) = (X13))
% 0.37/0.55          | ~ (r1_tarski @ X13 @ X11)
% 0.37/0.55          | ~ (r1_tarski @ X11 @ X13))),
% 0.37/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.55  thf('67', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((X0) = (k1_xboole_0))
% 0.37/0.55          | ~ (r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.37/0.55          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.55  thf('68', plain,
% 0.37/0.55      ((~ (r1_tarski @ sk_C_2 @ (k1_tarski @ (k3_tarski @ sk_B_1)))
% 0.37/0.55        | ((sk_C_2) = (k1_tarski @ (sk_B @ sk_C_2)))
% 0.37/0.55        | ((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['62', '67'])).
% 0.37/0.55  thf('69', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['45', '58'])).
% 0.37/0.55  thf('70', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('71', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.37/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.37/0.55  thf('72', plain, ((r1_tarski @ sk_C_2 @ (k1_tarski @ sk_A))),
% 0.37/0.55      inference('sup+', [status(thm)], ['70', '71'])).
% 0.37/0.55  thf('73', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['17', '38'])).
% 0.37/0.55  thf('74', plain, ((r1_tarski @ sk_C_2 @ sk_B_1)),
% 0.37/0.55      inference('demod', [status(thm)], ['72', '73'])).
% 0.37/0.55  thf('75', plain, (((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['44', '61'])).
% 0.37/0.55  thf('76', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.37/0.55      inference('demod', [status(thm)], ['45', '58'])).
% 0.37/0.55  thf('77', plain, ((((sk_C_2) = (sk_B_1)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.37/0.55      inference('demod', [status(thm)], ['68', '69', '74', '75', '76'])).
% 0.37/0.55  thf('78', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('79', plain, (((sk_B_1) != (sk_C_2))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('80', plain, ($false),
% 0.37/0.55      inference('simplify_reflect-', [status(thm)], ['77', '78', '79'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
