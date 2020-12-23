%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qOSjSoHvMC

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  213 ( 272 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X8 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X8 @ X9 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ( r1_tarski @ ( k5_relat_1 @ X7 @ X6 ) @ ( k5_relat_1 @ X7 @ X5 ) )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t93_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( r1_tarski @ ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) @ ( k5_relat_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( r1_tarski @ ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) @ ( k5_relat_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t93_relat_1])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) ) @ ( k5_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['13','14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qOSjSoHvMC
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:28:39 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 12 iterations in 0.013s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(t88_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X8 : $i, X9 : $i]:
% 0.20/0.45         ((r1_tarski @ (k7_relat_1 @ X8 @ X9) @ X8) | ~ (v1_relat_1 @ X8))),
% 0.20/0.45      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.20/0.45  thf(t3_subset, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X0 : $i, X2 : $i]:
% 0.20/0.45         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(cc2_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.45          | (v1_relat_1 @ X3)
% 0.20/0.45          | ~ (v1_relat_1 @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X8 : $i, X9 : $i]:
% 0.20/0.45         ((r1_tarski @ (k7_relat_1 @ X8 @ X9) @ X8) | ~ (v1_relat_1 @ X8))),
% 0.20/0.45      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.20/0.45  thf(t48_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( v1_relat_1 @ B ) =>
% 0.20/0.45           ( ![C:$i]:
% 0.20/0.45             ( ( v1_relat_1 @ C ) =>
% 0.20/0.45               ( ( r1_tarski @ A @ B ) =>
% 0.20/0.45                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X5)
% 0.20/0.45          | ~ (r1_tarski @ X6 @ X5)
% 0.20/0.45          | (r1_tarski @ (k5_relat_1 @ X7 @ X6) @ (k5_relat_1 @ X7 @ X5))
% 0.20/0.45          | ~ (v1_relat_1 @ X7)
% 0.20/0.45          | ~ (v1_relat_1 @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [t48_relat_1])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.45          | ~ (v1_relat_1 @ X2)
% 0.20/0.45          | (r1_tarski @ (k5_relat_1 @ X2 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.20/0.45             (k5_relat_1 @ X2 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         ((r1_tarski @ (k5_relat_1 @ X2 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.20/0.45           (k5_relat_1 @ X2 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ X2)
% 0.20/0.45          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X1)
% 0.20/0.45          | ~ (v1_relat_1 @ X1)
% 0.20/0.45          | ~ (v1_relat_1 @ X2)
% 0.20/0.45          | (r1_tarski @ (k5_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.20/0.45             (k5_relat_1 @ X2 @ X1)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         ((r1_tarski @ (k5_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.20/0.45           (k5_relat_1 @ X2 @ X1))
% 0.20/0.45          | ~ (v1_relat_1 @ X2)
% 0.20/0.45          | ~ (v1_relat_1 @ X1))),
% 0.20/0.45      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.45  thf(t93_relat_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ![C:$i]:
% 0.20/0.45         ( ( v1_relat_1 @ C ) =>
% 0.20/0.45           ( r1_tarski @
% 0.20/0.45             ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) @ 
% 0.20/0.45             ( k5_relat_1 @ B @ C ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i]:
% 0.20/0.45        ( ( v1_relat_1 @ B ) =>
% 0.20/0.45          ( ![C:$i]:
% 0.20/0.45            ( ( v1_relat_1 @ C ) =>
% 0.20/0.45              ( r1_tarski @
% 0.20/0.45                ( k5_relat_1 @ B @ ( k7_relat_1 @ C @ A ) ) @ 
% 0.20/0.45                ( k5_relat_1 @ B @ C ) ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t93_relat_1])).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (~ (r1_tarski @ (k5_relat_1 @ sk_B @ (k7_relat_1 @ sk_C @ sk_A)) @ 
% 0.20/0.45          (k5_relat_1 @ sk_B @ sk_C))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('13', plain, ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('16', plain, ($false),
% 0.20/0.45      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
