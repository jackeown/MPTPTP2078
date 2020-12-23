%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TV3zzjS83H

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  41 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  198 ( 382 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    r1_xboole_0 @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['6','11'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['5','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TV3zzjS83H
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 94 iterations in 0.031s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(t47_subset_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48           ( ![D:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48               ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 0.20/0.48                 ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48          ( ![C:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48              ( ![D:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48                  ( ( ( r1_tarski @ B @ C ) & ( r1_xboole_0 @ D @ C ) ) =>
% 0.20/0.48                    ( r1_tarski @ B @ ( k3_subset_1 @ A @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t47_subset_1])).
% 0.20/0.48  thf('0', plain, (~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t43_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.20/0.48             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.48          | ~ (r1_xboole_0 @ X10 @ X8)
% 0.20/0.48          | (r1_tarski @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.48          | (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_D))
% 0.20/0.48          | ~ (r1_xboole_0 @ X0 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((~ (r1_xboole_0 @ sk_B @ sk_D)
% 0.20/0.48        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('6', plain, ((r1_xboole_0 @ sk_D @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t12_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.48  thf('9', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(t70_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.48            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.48       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.48            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X4 @ X5)
% 0.20/0.48          | ~ (r1_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_C) | (r1_xboole_0 @ X0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '11'])).
% 0.20/0.48  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.48  thf('14', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_D))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '14'])).
% 0.20/0.48  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
