%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hbqo2g7KvE

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:02 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 104 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  466 ( 647 expanded)
%              Number of equality atoms :   49 (  70 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X47: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X47 @ X49 ) @ X50 )
      | ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( r2_hidden @ X47 @ X50 ) ) ),
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
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( ( k3_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X4 )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X4 )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X24: $i] :
      ( ( k2_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X30 @ X31 ) @ X31 )
      = ( k4_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ( X19 != X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X20: $i] :
      ( r1_tarski @ X20 @ X20 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

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

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X15 @ X16 )
      | ( r2_hidden @ ( sk_C @ X16 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X32: $i,X34: $i] :
      ( ( r1_xboole_0 @ X32 @ X34 )
      | ( ( k4_xboole_0 @ X32 @ X34 )
       != X32 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X20: $i] :
      ( r1_tarski @ X20 @ X20 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('36',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ X47 @ X48 )
      | ~ ( r1_tarski @ ( k2_tarski @ X47 @ X49 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k4_xboole_0 @ X32 @ X33 )
        = X32 )
      | ~ ( r1_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','25','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','44'])).

thf('46',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X28 ) )
      = ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X24: $i] :
      ( ( k2_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('49',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('52',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hbqo2g7KvE
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:24:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.07/1.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.26  % Solved by: fo/fo7.sh
% 1.07/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.26  % done 1015 iterations in 0.785s
% 1.07/1.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.26  % SZS output start Refutation
% 1.07/1.26  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.07/1.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.26  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.07/1.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.07/1.26  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.07/1.26  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.07/1.26  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.07/1.26  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.07/1.26  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.07/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.26  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.07/1.26  thf(t46_zfmisc_1, conjecture,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( r2_hidden @ A @ B ) =>
% 1.07/1.26       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 1.07/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.26    (~( ![A:$i,B:$i]:
% 1.07/1.26        ( ( r2_hidden @ A @ B ) =>
% 1.07/1.26          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 1.07/1.26    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 1.07/1.26  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(t38_zfmisc_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.07/1.26       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.07/1.26  thf('2', plain,
% 1.07/1.26      (![X47 : $i, X49 : $i, X50 : $i]:
% 1.07/1.26         ((r1_tarski @ (k2_tarski @ X47 @ X49) @ X50)
% 1.07/1.26          | ~ (r2_hidden @ X49 @ X50)
% 1.07/1.26          | ~ (r2_hidden @ X47 @ X50))),
% 1.07/1.26      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.07/1.26  thf('3', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.07/1.26          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 1.07/1.26      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.26  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1)),
% 1.07/1.26      inference('sup-', [status(thm)], ['0', '3'])).
% 1.07/1.26  thf(t69_enumset1, axiom,
% 1.07/1.26    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.07/1.26  thf('5', plain, (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 1.07/1.26      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.07/1.26  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 1.07/1.26      inference('demod', [status(thm)], ['4', '5'])).
% 1.07/1.26  thf(t28_xboole_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.07/1.26  thf('7', plain,
% 1.07/1.26      (![X25 : $i, X26 : $i]:
% 1.07/1.26         (((k3_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_tarski @ X25 @ X26))),
% 1.07/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.07/1.26  thf('8', plain,
% 1.07/1.26      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 1.07/1.26      inference('sup-', [status(thm)], ['6', '7'])).
% 1.07/1.26  thf(commutativity_k3_xboole_0, axiom,
% 1.07/1.26    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.07/1.26  thf('9', plain,
% 1.07/1.26      (![X4 : $i, X5 : $i]: ((k3_xboole_0 @ X5 @ X4) = (k3_xboole_0 @ X4 @ X5))),
% 1.07/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.26  thf('10', plain,
% 1.07/1.26      (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.07/1.26      inference('demod', [status(thm)], ['8', '9'])).
% 1.07/1.26  thf('11', plain,
% 1.07/1.26      (![X4 : $i, X5 : $i]: ((k3_xboole_0 @ X5 @ X4) = (k3_xboole_0 @ X4 @ X5))),
% 1.07/1.26      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.26  thf(t100_xboole_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.07/1.26  thf('12', plain,
% 1.07/1.26      (![X22 : $i, X23 : $i]:
% 1.07/1.26         ((k4_xboole_0 @ X22 @ X23)
% 1.07/1.26           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 1.07/1.26      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.26  thf('13', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         ((k4_xboole_0 @ X0 @ X1)
% 1.07/1.26           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['11', '12'])).
% 1.07/1.26  thf('14', plain,
% 1.07/1.26      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.07/1.26         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['10', '13'])).
% 1.07/1.26  thf(commutativity_k2_xboole_0, axiom,
% 1.07/1.26    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.07/1.26  thf('15', plain,
% 1.07/1.26      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 1.07/1.26      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.07/1.26  thf(t1_boole, axiom,
% 1.07/1.26    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.07/1.26  thf('16', plain, (![X24 : $i]: ((k2_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 1.07/1.26      inference('cnf', [status(esa)], [t1_boole])).
% 1.07/1.26  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.07/1.26      inference('sup+', [status(thm)], ['15', '16'])).
% 1.07/1.26  thf(t40_xboole_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.07/1.26  thf('18', plain,
% 1.07/1.26      (![X30 : $i, X31 : $i]:
% 1.07/1.26         ((k4_xboole_0 @ (k2_xboole_0 @ X30 @ X31) @ X31)
% 1.07/1.26           = (k4_xboole_0 @ X30 @ X31))),
% 1.07/1.26      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.07/1.26  thf('19', plain,
% 1.07/1.26      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.07/1.26      inference('sup+', [status(thm)], ['17', '18'])).
% 1.07/1.26  thf(d10_xboole_0, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.07/1.26  thf('20', plain,
% 1.07/1.26      (![X19 : $i, X20 : $i]: ((r1_tarski @ X19 @ X20) | ((X19) != (X20)))),
% 1.07/1.26      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.07/1.26  thf('21', plain, (![X20 : $i]: (r1_tarski @ X20 @ X20)),
% 1.07/1.26      inference('simplify', [status(thm)], ['20'])).
% 1.07/1.26  thf('22', plain,
% 1.07/1.26      (![X25 : $i, X26 : $i]:
% 1.07/1.26         (((k3_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_tarski @ X25 @ X26))),
% 1.07/1.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.07/1.26  thf('23', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['21', '22'])).
% 1.07/1.26  thf('24', plain,
% 1.07/1.26      (![X22 : $i, X23 : $i]:
% 1.07/1.26         ((k4_xboole_0 @ X22 @ X23)
% 1.07/1.26           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 1.07/1.26      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.26  thf('25', plain,
% 1.07/1.26      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.07/1.26      inference('sup+', [status(thm)], ['23', '24'])).
% 1.07/1.26  thf(t3_xboole_0, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.07/1.26            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.07/1.26       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.07/1.26            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.07/1.26  thf('26', plain,
% 1.07/1.26      (![X15 : $i, X16 : $i]:
% 1.07/1.26         ((r1_xboole_0 @ X15 @ X16) | (r2_hidden @ (sk_C @ X16 @ X15) @ X15))),
% 1.07/1.26      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.07/1.26  thf(t39_xboole_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.07/1.26  thf('27', plain,
% 1.07/1.26      (![X28 : $i, X29 : $i]:
% 1.07/1.26         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 1.07/1.26           = (k2_xboole_0 @ X28 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.07/1.26  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.07/1.26      inference('sup+', [status(thm)], ['15', '16'])).
% 1.07/1.26  thf('29', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.07/1.26      inference('sup+', [status(thm)], ['27', '28'])).
% 1.07/1.26  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.07/1.26      inference('sup+', [status(thm)], ['15', '16'])).
% 1.07/1.26  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.07/1.26      inference('sup+', [status(thm)], ['29', '30'])).
% 1.07/1.26  thf(t83_xboole_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.07/1.26  thf('32', plain,
% 1.07/1.26      (![X32 : $i, X34 : $i]:
% 1.07/1.26         ((r1_xboole_0 @ X32 @ X34) | ((k4_xboole_0 @ X32 @ X34) != (X32)))),
% 1.07/1.26      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.07/1.26  thf('33', plain,
% 1.07/1.26      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['31', '32'])).
% 1.07/1.26  thf('34', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.07/1.26      inference('simplify', [status(thm)], ['33'])).
% 1.07/1.26  thf('35', plain, (![X20 : $i]: (r1_tarski @ X20 @ X20)),
% 1.07/1.26      inference('simplify', [status(thm)], ['20'])).
% 1.07/1.26  thf('36', plain,
% 1.07/1.26      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.07/1.26         ((r2_hidden @ X47 @ X48)
% 1.07/1.26          | ~ (r1_tarski @ (k2_tarski @ X47 @ X49) @ X48))),
% 1.07/1.26      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.07/1.26  thf('37', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['35', '36'])).
% 1.07/1.26  thf('38', plain,
% 1.07/1.26      (![X15 : $i, X17 : $i, X18 : $i]:
% 1.07/1.26         (~ (r2_hidden @ X17 @ X15)
% 1.07/1.26          | ~ (r2_hidden @ X17 @ X18)
% 1.07/1.26          | ~ (r1_xboole_0 @ X15 @ X18))),
% 1.07/1.26      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.07/1.26  thf('39', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 1.07/1.26          | ~ (r2_hidden @ X1 @ X2))),
% 1.07/1.26      inference('sup-', [status(thm)], ['37', '38'])).
% 1.07/1.26  thf('40', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.07/1.26      inference('sup-', [status(thm)], ['34', '39'])).
% 1.07/1.26  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.07/1.26      inference('sup-', [status(thm)], ['26', '40'])).
% 1.07/1.26  thf('42', plain,
% 1.07/1.26      (![X32 : $i, X33 : $i]:
% 1.07/1.26         (((k4_xboole_0 @ X32 @ X33) = (X32)) | ~ (r1_xboole_0 @ X32 @ X33))),
% 1.07/1.26      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.07/1.26  thf('43', plain,
% 1.07/1.26      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.07/1.26      inference('sup-', [status(thm)], ['41', '42'])).
% 1.07/1.26  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.07/1.26      inference('demod', [status(thm)], ['19', '25', '43'])).
% 1.07/1.26  thf('45', plain,
% 1.07/1.26      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 1.07/1.26      inference('demod', [status(thm)], ['14', '44'])).
% 1.07/1.26  thf('46', plain,
% 1.07/1.26      (![X28 : $i, X29 : $i]:
% 1.07/1.26         ((k2_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X28))
% 1.07/1.26           = (k2_xboole_0 @ X28 @ X29))),
% 1.07/1.26      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.07/1.26  thf('47', plain,
% 1.07/1.26      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 1.07/1.26         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 1.07/1.26      inference('sup+', [status(thm)], ['45', '46'])).
% 1.07/1.26  thf('48', plain, (![X24 : $i]: ((k2_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 1.07/1.26      inference('cnf', [status(esa)], [t1_boole])).
% 1.07/1.26  thf('49', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 1.07/1.26      inference('demod', [status(thm)], ['47', '48'])).
% 1.07/1.26  thf('50', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('51', plain,
% 1.07/1.26      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 1.07/1.26      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.07/1.26  thf('52', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 1.07/1.26      inference('demod', [status(thm)], ['50', '51'])).
% 1.07/1.26  thf('53', plain, ($false),
% 1.07/1.26      inference('simplify_reflect-', [status(thm)], ['49', '52'])).
% 1.07/1.26  
% 1.07/1.26  % SZS output end Refutation
% 1.07/1.26  
% 1.07/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
