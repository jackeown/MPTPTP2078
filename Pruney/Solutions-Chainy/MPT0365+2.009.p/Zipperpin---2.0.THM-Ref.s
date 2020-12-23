%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NqUHcOcmfK

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:07 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   54 (  71 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  377 ( 732 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t46_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( ( r1_xboole_0 @ B @ C )
              & ( r1_xboole_0 @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) )
           => ( B
              = ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( ( r1_xboole_0 @ B @ C )
                & ( r1_xboole_0 @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) )
             => ( B
                = ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
        = X17 )
      | ~ ( r1_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ ( k4_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,
    ( sk_A
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['5','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('23',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,
    ( sk_C
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['2','30'])).

thf('32',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NqUHcOcmfK
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.06/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.24  % Solved by: fo/fo7.sh
% 1.06/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.24  % done 2302 iterations in 0.777s
% 1.06/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.24  % SZS output start Refutation
% 1.06/1.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.24  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.06/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.24  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.06/1.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.24  thf(t46_subset_1, conjecture,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24       ( ![C:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24           ( ( ( r1_xboole_0 @ B @ C ) & 
% 1.06/1.24               ( r1_xboole_0 @
% 1.06/1.24                 ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 1.06/1.24             ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.06/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.24    (~( ![A:$i,B:$i]:
% 1.06/1.24        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24          ( ![C:$i]:
% 1.06/1.24            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24              ( ( ( r1_xboole_0 @ B @ C ) & 
% 1.06/1.24                  ( r1_xboole_0 @
% 1.06/1.24                    ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 1.06/1.24                ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 1.06/1.24    inference('cnf.neg', [status(esa)], [t46_subset_1])).
% 1.06/1.24  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(involutiveness_k3_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.06/1.24  thf('1', plain,
% 1.06/1.24      (![X23 : $i, X24 : $i]:
% 1.06/1.24         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 1.06/1.24          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.06/1.24      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.06/1.24  thf('2', plain,
% 1.06/1.24      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.24      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.24  thf('3', plain,
% 1.06/1.24      ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ (k3_subset_1 @ sk_A @ sk_C))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(t88_xboole_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( r1_xboole_0 @ A @ B ) =>
% 1.06/1.24       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 1.06/1.24  thf('4', plain,
% 1.06/1.24      (![X17 : $i, X18 : $i]:
% 1.06/1.24         (((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18) = (X17))
% 1.06/1.24          | ~ (r1_xboole_0 @ X17 @ X18))),
% 1.06/1.24      inference('cnf', [status(esa)], [t88_xboole_1])).
% 1.06/1.24  thf('5', plain,
% 1.06/1.24      (((k4_xboole_0 @ 
% 1.06/1.24         (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 1.06/1.24          (k3_subset_1 @ sk_A @ sk_C)) @ 
% 1.06/1.24         (k3_subset_1 @ sk_A @ sk_C)) = (k3_subset_1 @ sk_A @ sk_B))),
% 1.06/1.24      inference('sup-', [status(thm)], ['3', '4'])).
% 1.06/1.24  thf('6', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(d5_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.06/1.24  thf('7', plain,
% 1.06/1.24      (![X19 : $i, X20 : $i]:
% 1.06/1.24         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 1.06/1.24          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 1.06/1.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.24  thf('8', plain,
% 1.06/1.24      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 1.06/1.24      inference('sup-', [status(thm)], ['6', '7'])).
% 1.06/1.24  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('10', plain,
% 1.06/1.24      (![X19 : $i, X20 : $i]:
% 1.06/1.24         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 1.06/1.24          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 1.06/1.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.24  thf('11', plain,
% 1.06/1.24      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.06/1.24      inference('sup-', [status(thm)], ['9', '10'])).
% 1.06/1.24  thf(l36_xboole_1, axiom,
% 1.06/1.24    (![A:$i,B:$i,C:$i]:
% 1.06/1.24     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 1.06/1.24       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 1.06/1.24  thf('12', plain,
% 1.06/1.24      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.06/1.24         ((k4_xboole_0 @ X3 @ (k3_xboole_0 @ X4 @ X5))
% 1.06/1.24           = (k2_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ (k4_xboole_0 @ X3 @ X5)))),
% 1.06/1.24      inference('cnf', [status(esa)], [l36_xboole_1])).
% 1.06/1.24  thf('13', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 1.06/1.24           = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 1.06/1.24              (k4_xboole_0 @ sk_A @ X0)))),
% 1.06/1.24      inference('sup+', [status(thm)], ['11', '12'])).
% 1.06/1.24  thf('14', plain,
% 1.06/1.24      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 1.06/1.24         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 1.06/1.24            (k3_subset_1 @ sk_A @ sk_C)))),
% 1.06/1.24      inference('sup+', [status(thm)], ['8', '13'])).
% 1.06/1.24  thf('15', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(d7_xboole_0, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.06/1.24       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.06/1.24  thf('16', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.06/1.24      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.06/1.24  thf('17', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['15', '16'])).
% 1.06/1.24  thf(t3_boole, axiom,
% 1.06/1.24    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.24  thf('18', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 1.06/1.24      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.24  thf('19', plain,
% 1.06/1.24      (((sk_A)
% 1.06/1.24         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 1.06/1.24            (k3_subset_1 @ sk_A @ sk_C)))),
% 1.06/1.24      inference('demod', [status(thm)], ['14', '17', '18'])).
% 1.06/1.24  thf('20', plain,
% 1.06/1.24      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 1.06/1.24         = (k3_subset_1 @ sk_A @ sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['5', '19'])).
% 1.06/1.24  thf('21', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(dt_k3_subset_1, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.24       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.06/1.24  thf('22', plain,
% 1.06/1.24      (![X21 : $i, X22 : $i]:
% 1.06/1.24         ((m1_subset_1 @ (k3_subset_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 1.06/1.24          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 1.06/1.24      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.06/1.24  thf('23', plain,
% 1.06/1.24      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['21', '22'])).
% 1.06/1.24  thf('24', plain,
% 1.06/1.24      (![X19 : $i, X20 : $i]:
% 1.06/1.24         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 1.06/1.24          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 1.06/1.24      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.24  thf('25', plain,
% 1.06/1.24      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 1.06/1.24         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['23', '24'])).
% 1.06/1.24  thf('26', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('27', plain,
% 1.06/1.24      (![X23 : $i, X24 : $i]:
% 1.06/1.24         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 1.06/1.24          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.06/1.24      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.06/1.24  thf('28', plain,
% 1.06/1.24      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 1.06/1.24      inference('sup-', [status(thm)], ['26', '27'])).
% 1.06/1.24  thf('29', plain,
% 1.06/1.24      (((sk_C) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 1.06/1.24      inference('demod', [status(thm)], ['25', '28'])).
% 1.06/1.24  thf('30', plain, (((sk_C) = (k3_subset_1 @ sk_A @ sk_B))),
% 1.06/1.24      inference('sup+', [status(thm)], ['20', '29'])).
% 1.06/1.24  thf('31', plain, (((k3_subset_1 @ sk_A @ sk_C) = (sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['2', '30'])).
% 1.06/1.24  thf('32', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('33', plain, ($false),
% 1.06/1.24      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 1.06/1.24  
% 1.06/1.24  % SZS output end Refutation
% 1.06/1.24  
% 1.06/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
