%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LGEZAila0h

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  291 ( 440 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('2',plain,(
    r2_hidden @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X14 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_C @ sk_C ) @ sk_D ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    r1_tarski @ ( k1_tarski @ sk_C ) @ sk_D ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X14 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf(t119_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t119_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ X1 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    m1_subset_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X11 @ X12 ) )
      = ( k2_tarski @ ( k4_tarski @ X10 @ X11 ) @ ( k4_tarski @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LGEZAila0h
% 0.16/0.37  % Computer   : n022.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:07:11 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 60 iterations in 0.031s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(t8_relset_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ D ) ) =>
% 0.22/0.51       ( m1_subset_1 @
% 0.22/0.51         ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ 
% 0.22/0.51         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ D ) ) =>
% 0.22/0.51          ( m1_subset_1 @
% 0.22/0.51            ( k1_tarski @ ( k4_tarski @ A @ C ) ) @ 
% 0.22/0.51            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ D ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t8_relset_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (~ (m1_subset_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C)) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain, ((r2_hidden @ sk_C @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('2', plain, ((r2_hidden @ sk_C @ sk_D)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t38_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.22/0.51         ((r1_tarski @ (k2_tarski @ X14 @ X16) @ X17)
% 0.22/0.51          | ~ (r2_hidden @ X16 @ X17)
% 0.22/0.51          | ~ (r2_hidden @ X14 @ X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ sk_D)
% 0.22/0.51          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.51  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_C @ sk_C) @ sk_D)),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.51  thf(t69_enumset1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.51  thf('6', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('7', plain, ((r1_tarski @ (k1_tarski @ sk_C) @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.51  thf('8', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.22/0.51         ((r1_tarski @ (k2_tarski @ X14 @ X16) @ X17)
% 0.22/0.51          | ~ (r2_hidden @ X16 @ X17)
% 0.22/0.51          | ~ (r2_hidden @ X14 @ X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X0 @ sk_B)
% 0.22/0.51          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '11'])).
% 0.22/0.51  thf('13', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('14', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf(t119_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.22/0.51       ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.51         (~ (r1_tarski @ X6 @ X7)
% 0.22/0.51          | ~ (r1_tarski @ X8 @ X9)
% 0.22/0.51          | (r1_tarski @ (k2_zfmisc_1 @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X9)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t119_zfmisc_1])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_tarski @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ X1) @ 
% 0.22/0.51           (k2_zfmisc_1 @ sk_B @ X0))
% 0.22/0.51          | ~ (r1_tarski @ X1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      ((r1_tarski @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C)) @ 
% 0.22/0.51        (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '16'])).
% 0.22/0.51  thf(t3_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X18 : $i, X20 : $i]:
% 0.22/0.51         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      ((m1_subset_1 @ 
% 0.22/0.51        (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C)) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('20', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf(t36_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.22/0.51         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.22/0.51       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.22/0.51         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.51         ((k2_zfmisc_1 @ (k1_tarski @ X10) @ (k2_tarski @ X11 @ X12))
% 0.22/0.51           = (k2_tarski @ (k4_tarski @ X10 @ X11) @ (k4_tarski @ X10 @ X12)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.22/0.51           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf('23', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.22/0.51           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      ((m1_subset_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_C)) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['19', '24'])).
% 0.22/0.51  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
