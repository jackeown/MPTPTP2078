%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pK6FqfIFqE

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:09 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  250 ( 442 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t47_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( r1_xboole_0 @ D @ C ) )
               => ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( ( r1_tarski @ B @ C )
                    & ( r1_xboole_0 @ D @ C ) )
                 => ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_xboole_0 @ X13 @ X11 )
      | ( r1_tarski @ X13 @ ( k3_subset_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_D ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_D )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['5','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pK6FqfIFqE
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:55:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.36/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.61  % Solved by: fo/fo7.sh
% 0.36/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.61  % done 164 iterations in 0.148s
% 0.36/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.61  % SZS output start Refutation
% 0.36/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.61  thf(t47_subset_1, conjecture,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61       ( ![C:$i]:
% 0.36/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61           ( ![D:$i]:
% 0.36/0.61             ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61               ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 0.36/0.61                 ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.61    (~( ![A:$i,B:$i]:
% 0.36/0.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61          ( ![C:$i]:
% 0.36/0.61            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61              ( ![D:$i]:
% 0.36/0.61                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61                  ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 0.36/0.61                    ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ) )),
% 0.36/0.61    inference('cnf.neg', [status(esa)], [t47_subset_1])).
% 0.36/0.61  thf('0', plain, (~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('2', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t43_subset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61       ( ![C:$i]:
% 0.36/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.61           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.36/0.61             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.36/0.61  thf('3', plain,
% 0.36/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.36/0.61          | ~ (r1_xboole_0 @ X13 @ X11)
% 0.36/0.61          | (r1_tarski @ X13 @ (k3_subset_1 @ X12 @ X11))
% 0.36/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.36/0.61  thf('4', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.36/0.61          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_D))
% 0.36/0.61          | ~ (r1_xboole_0 @ X0 @ sk_D))),
% 0.36/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.61  thf('5', plain,
% 0.36/0.61      ((~ (r1_xboole_0 @ sk_B @ sk_D)
% 0.36/0.61        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.61  thf('6', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(symmetry_r1_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.36/0.61  thf('7', plain,
% 0.36/0.61      (![X3 : $i, X4 : $i]:
% 0.36/0.61         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.36/0.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.36/0.61  thf('8', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.36/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.61  thf(d7_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.36/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.61  thf('9', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.61  thf('10', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.61  thf('11', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t28_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.61  thf('12', plain,
% 0.36/0.61      (![X8 : $i, X9 : $i]:
% 0.36/0.61         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.36/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.61  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.36/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.61  thf(t16_xboole_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.61       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.36/0.61  thf('14', plain,
% 0.36/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.36/0.61           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.36/0.61  thf('15', plain,
% 0.36/0.61      (![X0 : $i]:
% 0.36/0.61         ((k3_xboole_0 @ sk_B @ X0)
% 0.36/0.61           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.36/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.36/0.61  thf('16', plain,
% 0.36/0.61      (((k3_xboole_0 @ sk_B @ sk_D) = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.36/0.61      inference('sup+', [status(thm)], ['10', '15'])).
% 0.36/0.61  thf(t2_boole, axiom,
% 0.36/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.61  thf('17', plain,
% 0.36/0.61      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.36/0.61  thf('18', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.36/0.61      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.61  thf('19', plain,
% 0.36/0.61      (![X0 : $i, X2 : $i]:
% 0.36/0.61         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.36/0.61  thf('20', plain,
% 0.36/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_D))),
% 0.36/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.61  thf('21', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.36/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.36/0.61  thf('22', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D))),
% 0.36/0.61      inference('demod', [status(thm)], ['5', '21'])).
% 0.36/0.61  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.36/0.61  
% 0.36/0.61  % SZS output end Refutation
% 0.36/0.61  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
