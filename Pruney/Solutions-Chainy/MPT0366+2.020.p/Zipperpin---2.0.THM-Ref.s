%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lstDVs8zHC

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  187 ( 371 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_xboole_0 @ X10 @ X8 )
      | ( r1_tarski @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('9',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C )
      | ( r1_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['5','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lstDVs8zHC
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.44  % Solved by: fo/fo7.sh
% 0.21/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.44  % done 38 iterations in 0.017s
% 0.21/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.44  % SZS output start Refutation
% 0.21/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.44  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.44  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.44  thf(t47_subset_1, conjecture,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.44       ( ![C:$i]:
% 0.21/0.44         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.44           ( ![D:$i]:
% 0.21/0.44             ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.44               ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 0.21/0.44                 ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ))).
% 0.21/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.44    (~( ![A:$i,B:$i]:
% 0.21/0.44        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.44          ( ![C:$i]:
% 0.21/0.44            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.44              ( ![D:$i]:
% 0.21/0.44                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.44                  ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 0.21/0.44                    ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ) )),
% 0.21/0.44    inference('cnf.neg', [status(esa)], [t47_subset_1])).
% 0.21/0.44  thf('0', plain, (~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('2', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(t43_subset_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.44       ( ![C:$i]:
% 0.21/0.44         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.44           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.21/0.44             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.44  thf('3', plain,
% 0.21/0.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.44         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.21/0.44          | ~ (r1_xboole_0 @ X10 @ X8)
% 0.21/0.44          | (r1_tarski @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.21/0.44          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.21/0.44  thf('4', plain,
% 0.21/0.44      (![X0 : $i]:
% 0.21/0.44         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.44          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_D))
% 0.21/0.44          | ~ (r1_xboole_0 @ X0 @ sk_D))),
% 0.21/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.44  thf('5', plain,
% 0.21/0.44      ((~ (r1_xboole_0 @ sk_B @ sk_D)
% 0.21/0.44        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D)))),
% 0.21/0.44      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.44  thf('6', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf('7', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 0.21/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.44  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.44    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.44  thf('8', plain,
% 0.21/0.44      (![X0 : $i, X1 : $i]:
% 0.21/0.44         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.44      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.44  thf('9', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.21/0.44      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.44  thf(t83_xboole_1, axiom,
% 0.21/0.44    (![A:$i,B:$i]:
% 0.21/0.44     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.44  thf('10', plain,
% 0.21/0.44      (![X5 : $i, X6 : $i]:
% 0.21/0.44         (((k4_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.21/0.44      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.44  thf('11', plain, (((k4_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 0.21/0.44      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.44  thf(t106_xboole_1, axiom,
% 0.21/0.44    (![A:$i,B:$i,C:$i]:
% 0.21/0.44     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.21/0.44       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.21/0.44  thf('12', plain,
% 0.21/0.44      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.44         ((r1_xboole_0 @ X2 @ X4)
% 0.21/0.44          | ~ (r1_tarski @ X2 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.21/0.44      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.21/0.44  thf('13', plain,
% 0.21/0.44      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C) | (r1_xboole_0 @ X0 @ sk_D))),
% 0.21/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.44  thf('14', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.21/0.44      inference('sup-', [status(thm)], ['6', '13'])).
% 0.21/0.44  thf('15', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D))),
% 0.21/0.44      inference('demod', [status(thm)], ['5', '14'])).
% 0.21/0.44  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.21/0.44  
% 0.21/0.44  % SZS output end Refutation
% 0.21/0.44  
% 0.21/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
