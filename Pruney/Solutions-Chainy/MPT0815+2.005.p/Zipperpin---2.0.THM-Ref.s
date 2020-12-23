%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oUXWdduyLE

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  61 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  348 ( 441 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(t8_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ D ) )
     => ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ D ) )
       => ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X28 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ ( k1_tarski @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X28 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t119_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ~ ( r1_tarski @ X33 @ X34 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X31 @ X33 ) @ ( k2_zfmisc_1 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t119_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X35 @ X38 ) @ ( k2_tarski @ X36 @ X37 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X35 @ X36 ) @ ( k4_tarski @ X35 @ X37 ) @ ( k4_tarski @ X38 @ X36 ) @ ( k4_tarski @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_enumset1 @ X3 @ X3 @ X4 @ X5 )
      = ( k1_enumset1 @ X3 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_enumset1 @ ( k4_tarski @ X2 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X2 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k1_tarski @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X2 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X28 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('25',plain,(
    r1_tarski @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oUXWdduyLE
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 118 iterations in 0.068s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(t8_relset_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ D ) ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ 
% 0.21/0.52         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ D ) ) =>
% 0.21/0.52          ( m1_subset_1 @
% 0.21/0.52            ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ 
% 0.21/0.52            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t8_relset_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (~ (m1_subset_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C)) @ 
% 0.21/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((r2_hidden @ sk_C @ sk_D)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(l1_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X28 : $i, X30 : $i]:
% 0.21/0.52         ((r1_tarski @ (k1_tarski @ X28) @ X30) | ~ (r2_hidden @ X28 @ X30))),
% 0.21/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.52  thf('3', plain, ((r1_tarski @ (k1_tarski @ sk_C) @ sk_D)),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X28 : $i, X30 : $i]:
% 0.21/0.52         ((r1_tarski @ (k1_tarski @ X28) @ X30) | ~ (r2_hidden @ X28 @ X30))),
% 0.21/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.52  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf(t119_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.21/0.52       ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.52         (~ (r1_tarski @ X31 @ X32)
% 0.21/0.52          | ~ (r1_tarski @ X33 @ X34)
% 0.21/0.52          | (r1_tarski @ (k2_zfmisc_1 @ X31 @ X33) @ (k2_zfmisc_1 @ X32 @ X34)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t119_zfmisc_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tarski @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ X1) @ 
% 0.21/0.52           (k2_zfmisc_1 @ sk_B @ X0))
% 0.21/0.52          | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      ((r1_tarski @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C)) @ 
% 0.21/0.52        (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.52  thf(t69_enumset1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.52  thf('10', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf('11', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf(t146_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.21/0.52       ( k2_enumset1 @
% 0.21/0.52         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 0.21/0.52         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.52         ((k2_zfmisc_1 @ (k2_tarski @ X35 @ X38) @ (k2_tarski @ X36 @ X37))
% 0.21/0.52           = (k2_enumset1 @ (k4_tarski @ X35 @ X36) @ 
% 0.21/0.52              (k4_tarski @ X35 @ X37) @ (k4_tarski @ X38 @ X36) @ 
% 0.21/0.52              (k4_tarski @ X38 @ X37)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 0.21/0.52  thf(t71_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         ((k2_enumset1 @ X3 @ X3 @ X4 @ X5) = (k1_enumset1 @ X3 @ X4 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_zfmisc_1 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X0))
% 0.21/0.52           = (k1_enumset1 @ (k4_tarski @ X2 @ X0) @ (k4_tarski @ X1 @ X0) @ 
% 0.21/0.52              (k4_tarski @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf(t70_enumset1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         ((k1_enumset1 @ X1 @ X1 @ X2) = (k2_tarski @ X1 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.52  thf('16', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X28 : $i, X29 : $i]:
% 0.21/0.52         ((r2_hidden @ X28 @ X29) | ~ (r1_tarski @ (k1_tarski @ X28) @ X29))),
% 0.21/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k1_enumset1 @ X0 @ X0 @ X0) @ X1)
% 0.21/0.52          | (r2_hidden @ X0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_tarski @ 
% 0.21/0.52             (k2_zfmisc_1 @ (k2_tarski @ X1 @ X1) @ (k2_tarski @ X0 @ X0)) @ X2)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X1 @ X0) @ X2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_tarski @ 
% 0.21/0.52             (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X2)) @ X1)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X0 @ X2) @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r1_tarski @ (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k1_tarski @ X0)) @ 
% 0.21/0.52             X1)
% 0.21/0.52          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((r2_hidden @ (k4_tarski @ sk_A @ sk_C) @ (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X28 : $i, X30 : $i]:
% 0.21/0.52         ((r1_tarski @ (k1_tarski @ X28) @ X30) | ~ (r2_hidden @ X28 @ X30))),
% 0.21/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((r1_tarski @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C)) @ 
% 0.21/0.52        (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf(t3_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X39 : $i, X41 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C)) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
