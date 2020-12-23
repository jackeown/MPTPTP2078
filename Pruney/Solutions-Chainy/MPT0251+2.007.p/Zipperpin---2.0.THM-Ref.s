%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yYpBzCCbxj

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:02 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 137 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  508 ( 886 expanded)
%              Number of equality atoms :   51 (  97 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X49 )
      | ~ ( r2_hidden @ X48 @ X49 )
      | ~ ( r2_hidden @ X46 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X44 @ X45 ) )
      = ( k2_xboole_0 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X25 @ X26 ) @ X26 )
      = ( k4_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','26'])).

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

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_xboole_0 @ X29 @ X31 )
      | ( ( k4_xboole_0 @ X29 @ X31 )
       != X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('38',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('39',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( r2_hidden @ X46 @ X47 )
      | ~ ( r1_tarski @ ( k2_tarski @ X46 @ X48 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['28','46'])).

thf('48',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','50'])).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('53',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X20: $i] :
      ( ( k2_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('55',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('58',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yYpBzCCbxj
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.86/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.86/1.08  % Solved by: fo/fo7.sh
% 0.86/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.08  % done 2043 iterations in 0.628s
% 0.86/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.86/1.08  % SZS output start Refutation
% 0.86/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.86/1.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.86/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.08  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.86/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.86/1.08  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.86/1.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.86/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.86/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.86/1.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.86/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.86/1.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.86/1.08  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.86/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.86/1.08  thf(t46_zfmisc_1, conjecture,
% 0.86/1.08    (![A:$i,B:$i]:
% 0.86/1.08     ( ( r2_hidden @ A @ B ) =>
% 0.86/1.08       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.86/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.08    (~( ![A:$i,B:$i]:
% 0.86/1.08        ( ( r2_hidden @ A @ B ) =>
% 0.86/1.08          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.86/1.08    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.86/1.08  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.86/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.08  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.86/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.08  thf(t38_zfmisc_1, axiom,
% 0.86/1.08    (![A:$i,B:$i,C:$i]:
% 0.86/1.08     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.86/1.08       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.86/1.08  thf('2', plain,
% 0.86/1.08      (![X46 : $i, X48 : $i, X49 : $i]:
% 0.86/1.08         ((r1_tarski @ (k2_tarski @ X46 @ X48) @ X49)
% 0.86/1.08          | ~ (r2_hidden @ X48 @ X49)
% 0.86/1.08          | ~ (r2_hidden @ X46 @ X49))),
% 0.86/1.08      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.86/1.08  thf('3', plain,
% 0.86/1.08      (![X0 : $i]:
% 0.86/1.08         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.86/1.08          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 0.86/1.08      inference('sup-', [status(thm)], ['1', '2'])).
% 0.86/1.08  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1)),
% 0.86/1.08      inference('sup-', [status(thm)], ['0', '3'])).
% 0.86/1.08  thf(t69_enumset1, axiom,
% 0.86/1.08    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.86/1.08  thf('5', plain, (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.86/1.08      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.86/1.08  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.86/1.08      inference('demod', [status(thm)], ['4', '5'])).
% 0.86/1.08  thf(t28_xboole_1, axiom,
% 0.86/1.08    (![A:$i,B:$i]:
% 0.86/1.08     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.86/1.08  thf('7', plain,
% 0.86/1.08      (![X21 : $i, X22 : $i]:
% 0.86/1.08         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.86/1.08      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.86/1.08  thf('8', plain,
% 0.86/1.08      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.86/1.08      inference('sup-', [status(thm)], ['6', '7'])).
% 0.86/1.08  thf(t100_xboole_1, axiom,
% 0.86/1.08    (![A:$i,B:$i]:
% 0.86/1.08     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.86/1.08  thf('9', plain,
% 0.86/1.08      (![X18 : $i, X19 : $i]:
% 0.86/1.08         ((k4_xboole_0 @ X18 @ X19)
% 0.86/1.08           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.86/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.86/1.08  thf('10', plain,
% 0.86/1.08      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.86/1.08         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.86/1.08      inference('sup+', [status(thm)], ['8', '9'])).
% 0.86/1.08  thf(commutativity_k2_tarski, axiom,
% 0.86/1.08    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.86/1.08  thf('11', plain,
% 0.86/1.08      (![X32 : $i, X33 : $i]:
% 0.86/1.08         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 0.86/1.08      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.86/1.08  thf(l51_zfmisc_1, axiom,
% 0.86/1.08    (![A:$i,B:$i]:
% 0.86/1.08     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.86/1.08  thf('12', plain,
% 0.86/1.08      (![X44 : $i, X45 : $i]:
% 0.86/1.08         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 0.86/1.08      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.86/1.08  thf('13', plain,
% 0.86/1.08      (![X0 : $i, X1 : $i]:
% 0.86/1.08         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.08      inference('sup+', [status(thm)], ['11', '12'])).
% 0.86/1.08  thf('14', plain,
% 0.86/1.08      (![X44 : $i, X45 : $i]:
% 0.86/1.08         ((k3_tarski @ (k2_tarski @ X44 @ X45)) = (k2_xboole_0 @ X44 @ X45))),
% 0.86/1.08      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.86/1.08  thf('15', plain,
% 0.86/1.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.08      inference('sup+', [status(thm)], ['13', '14'])).
% 0.86/1.08  thf(t1_boole, axiom,
% 0.86/1.08    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.86/1.08  thf('16', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.86/1.08      inference('cnf', [status(esa)], [t1_boole])).
% 0.86/1.08  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.86/1.08      inference('sup+', [status(thm)], ['15', '16'])).
% 0.86/1.08  thf(t40_xboole_1, axiom,
% 0.86/1.08    (![A:$i,B:$i]:
% 0.86/1.08     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.86/1.08  thf('18', plain,
% 0.86/1.08      (![X25 : $i, X26 : $i]:
% 0.86/1.08         ((k4_xboole_0 @ (k2_xboole_0 @ X25 @ X26) @ X26)
% 0.86/1.08           = (k4_xboole_0 @ X25 @ X26))),
% 0.86/1.08      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.86/1.08  thf('19', plain,
% 0.86/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.86/1.08      inference('sup+', [status(thm)], ['17', '18'])).
% 0.86/1.08  thf('20', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.86/1.08      inference('cnf', [status(esa)], [t1_boole])).
% 0.86/1.08  thf(t7_xboole_1, axiom,
% 0.86/1.08    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.86/1.08  thf('21', plain,
% 0.86/1.08      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.86/1.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.86/1.08  thf('22', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.86/1.08      inference('sup+', [status(thm)], ['20', '21'])).
% 0.86/1.08  thf('23', plain,
% 0.86/1.08      (![X21 : $i, X22 : $i]:
% 0.86/1.08         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.86/1.08      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.86/1.08  thf('24', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.86/1.08      inference('sup-', [status(thm)], ['22', '23'])).
% 0.86/1.08  thf('25', plain,
% 0.86/1.08      (![X18 : $i, X19 : $i]:
% 0.86/1.08         ((k4_xboole_0 @ X18 @ X19)
% 0.86/1.08           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.86/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.86/1.08  thf('26', plain,
% 0.86/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.86/1.08      inference('sup+', [status(thm)], ['24', '25'])).
% 0.86/1.08  thf('27', plain,
% 0.86/1.08      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.86/1.08      inference('demod', [status(thm)], ['19', '26'])).
% 0.86/1.08  thf(t3_xboole_0, axiom,
% 0.86/1.08    (![A:$i,B:$i]:
% 0.86/1.08     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.86/1.08            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.86/1.08       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.86/1.08            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.86/1.08  thf('28', plain,
% 0.86/1.08      (![X11 : $i, X12 : $i]:
% 0.86/1.08         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C @ X12 @ X11) @ X11))),
% 0.86/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.86/1.08  thf(t39_xboole_1, axiom,
% 0.86/1.08    (![A:$i,B:$i]:
% 0.86/1.08     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.86/1.08  thf('29', plain,
% 0.86/1.08      (![X23 : $i, X24 : $i]:
% 0.86/1.08         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.86/1.08           = (k2_xboole_0 @ X23 @ X24))),
% 0.86/1.08      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.86/1.08  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.86/1.08      inference('sup+', [status(thm)], ['15', '16'])).
% 0.86/1.08  thf('31', plain,
% 0.86/1.08      (![X0 : $i]:
% 0.86/1.08         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.86/1.08      inference('sup+', [status(thm)], ['29', '30'])).
% 0.86/1.08  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.86/1.08      inference('sup+', [status(thm)], ['15', '16'])).
% 0.86/1.08  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.86/1.08      inference('sup+', [status(thm)], ['31', '32'])).
% 0.86/1.08  thf(t83_xboole_1, axiom,
% 0.86/1.08    (![A:$i,B:$i]:
% 0.86/1.08     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.86/1.08  thf('34', plain,
% 0.86/1.08      (![X29 : $i, X31 : $i]:
% 0.86/1.08         ((r1_xboole_0 @ X29 @ X31) | ((k4_xboole_0 @ X29 @ X31) != (X29)))),
% 0.86/1.08      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.86/1.08  thf('35', plain,
% 0.86/1.08      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.86/1.08      inference('sup-', [status(thm)], ['33', '34'])).
% 0.86/1.08  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.86/1.08      inference('simplify', [status(thm)], ['35'])).
% 0.86/1.08  thf('37', plain,
% 0.86/1.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.08      inference('sup+', [status(thm)], ['13', '14'])).
% 0.86/1.08  thf('38', plain,
% 0.86/1.08      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.86/1.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.86/1.08  thf('39', plain,
% 0.86/1.08      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.86/1.08      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.86/1.08  thf('40', plain,
% 0.86/1.08      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.86/1.08         ((r2_hidden @ X46 @ X47)
% 0.86/1.08          | ~ (r1_tarski @ (k2_tarski @ X46 @ X48) @ X47))),
% 0.86/1.08      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.86/1.08  thf('41', plain,
% 0.86/1.08      (![X0 : $i, X1 : $i]:
% 0.86/1.08         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.86/1.08      inference('sup-', [status(thm)], ['39', '40'])).
% 0.86/1.08  thf('42', plain,
% 0.86/1.08      (![X0 : $i, X1 : $i]:
% 0.86/1.08         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.86/1.08      inference('sup-', [status(thm)], ['38', '41'])).
% 0.86/1.08  thf('43', plain,
% 0.86/1.08      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.86/1.08         (~ (r2_hidden @ X13 @ X11)
% 0.86/1.08          | ~ (r2_hidden @ X13 @ X14)
% 0.86/1.08          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.86/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.86/1.08  thf('44', plain,
% 0.86/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.08         (~ (r1_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X2)
% 0.86/1.08          | ~ (r2_hidden @ X1 @ X2))),
% 0.86/1.08      inference('sup-', [status(thm)], ['42', '43'])).
% 0.86/1.08  thf('45', plain,
% 0.86/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.08         (~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 0.86/1.08          | ~ (r2_hidden @ X0 @ X2))),
% 0.86/1.08      inference('sup-', [status(thm)], ['37', '44'])).
% 0.86/1.08  thf('46', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.86/1.08      inference('sup-', [status(thm)], ['36', '45'])).
% 0.86/1.08  thf('47', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.86/1.08      inference('sup-', [status(thm)], ['28', '46'])).
% 0.86/1.08  thf('48', plain,
% 0.86/1.08      (![X29 : $i, X30 : $i]:
% 0.86/1.08         (((k4_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_xboole_0 @ X29 @ X30))),
% 0.86/1.08      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.86/1.08  thf('49', plain,
% 0.86/1.08      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.86/1.08      inference('sup-', [status(thm)], ['47', '48'])).
% 0.86/1.08  thf('50', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.86/1.08      inference('demod', [status(thm)], ['27', '49'])).
% 0.86/1.08  thf('51', plain,
% 0.86/1.08      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.86/1.08      inference('demod', [status(thm)], ['10', '50'])).
% 0.86/1.08  thf('52', plain,
% 0.86/1.08      (![X23 : $i, X24 : $i]:
% 0.86/1.08         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.86/1.08           = (k2_xboole_0 @ X23 @ X24))),
% 0.86/1.08      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.86/1.08  thf('53', plain,
% 0.86/1.08      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.86/1.08         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.86/1.08      inference('sup+', [status(thm)], ['51', '52'])).
% 0.86/1.08  thf('54', plain, (![X20 : $i]: ((k2_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.86/1.08      inference('cnf', [status(esa)], [t1_boole])).
% 0.86/1.08  thf('55', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.86/1.08      inference('demod', [status(thm)], ['53', '54'])).
% 0.86/1.08  thf('56', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.86/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.08  thf('57', plain,
% 0.86/1.08      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.86/1.08      inference('sup+', [status(thm)], ['13', '14'])).
% 0.86/1.08  thf('58', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.86/1.08      inference('demod', [status(thm)], ['56', '57'])).
% 0.86/1.08  thf('59', plain, ($false),
% 0.86/1.08      inference('simplify_reflect-', [status(thm)], ['55', '58'])).
% 0.86/1.08  
% 0.86/1.08  % SZS output end Refutation
% 0.86/1.08  
% 0.95/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
