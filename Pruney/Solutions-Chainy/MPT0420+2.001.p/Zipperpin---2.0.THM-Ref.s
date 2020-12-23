%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.83MUIU7MkV

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 113 expanded)
%              Number of leaves         :   11 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  442 (1445 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t52_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C )
          <=> ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C )
            <=> ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_setfam_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k7_setfam_1 @ X3 @ ( k7_setfam_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('7',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X5 @ X6 ) @ ( k7_setfam_1 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[t51_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('14',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('24',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X5 @ X6 ) @ ( k7_setfam_1 @ X5 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[t51_setfam_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_C ) ) )
      | ( r1_tarski @ X0 @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k7_setfam_1 @ X3 @ ( k7_setfam_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('29',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ X0 ) @ sk_C )
      | ( r1_tarski @ X0 @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,
    ( ( r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C )
    | ( r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,(
    r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','18','33'])).

thf('35',plain,(
    r1_tarski @ ( k7_setfam_1 @ sk_A @ sk_B ) @ sk_C ),
    inference(simpl_trail,[status(thm)],['32','34'])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( k7_setfam_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['31','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['20','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.83MUIU7MkV
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:20:31 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 31 iterations in 0.017s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.46  thf(t52_setfam_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C ) <=>
% 0.20/0.46             ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46          ( ![C:$i]:
% 0.20/0.46            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46              ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ C ) <=>
% 0.20/0.46                ( r1_tarski @ B @ ( k7_setfam_1 @ A @ C ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t52_setfam_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((~ (r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))
% 0.20/0.46        | ~ (r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((~ (r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C)))
% 0.20/0.46         <= (~ ((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (~ ((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))) | 
% 0.20/0.46       ~ ((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))
% 0.20/0.46        | (r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C)))
% 0.20/0.46         <= (((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(involutiveness_k7_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]:
% 0.20/0.46         (((k7_setfam_1 @ X3 @ (k7_setfam_1 @ X3 @ X2)) = (X2))
% 0.20/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.20/0.46      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t51_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 0.20/0.46             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5)))
% 0.20/0.46          | (r1_tarski @ X6 @ X4)
% 0.20/0.46          | ~ (r1_tarski @ (k7_setfam_1 @ X5 @ X6) @ (k7_setfam_1 @ X5 @ X4))
% 0.20/0.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.46      inference('cnf', [status(esa)], [t51_setfam_1])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.46          | ~ (r1_tarski @ (k7_setfam_1 @ sk_A @ X0) @ 
% 0.20/0.46               (k7_setfam_1 @ sk_A @ sk_C))
% 0.20/0.46          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((~ (r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))
% 0.20/0.46        | (r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C)
% 0.20/0.46        | ~ (m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.20/0.46             (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(dt_k7_setfam_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.46       ( m1_subset_1 @
% 0.20/0.46         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((m1_subset_1 @ (k7_setfam_1 @ X0 @ X1) @ 
% 0.20/0.46           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.20/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.20/0.46        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((~ (r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))
% 0.20/0.46        | (r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.46      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46         <= (((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      ((~ (r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46         <= (~ ((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C)) | 
% 0.20/0.46       ~ ((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain, (~ ((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['2', '18'])).
% 0.20/0.46  thf('20', plain, (~ (r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['1', '19'])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((m1_subset_1 @ (k7_setfam_1 @ X0 @ X1) @ 
% 0.20/0.46           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.20/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_C) @ 
% 0.20/0.46        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5)))
% 0.20/0.46          | (r1_tarski @ X6 @ X4)
% 0.20/0.46          | ~ (r1_tarski @ (k7_setfam_1 @ X5 @ X6) @ (k7_setfam_1 @ X5 @ X4))
% 0.20/0.46          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.46      inference('cnf', [status(esa)], [t51_setfam_1])).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.46          | ~ (r1_tarski @ (k7_setfam_1 @ sk_A @ X0) @ 
% 0.20/0.46               (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_C)))
% 0.20/0.46          | (r1_tarski @ X0 @ (k7_setfam_1 @ sk_A @ sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i]:
% 0.20/0.46         (((k7_setfam_1 @ X3 @ (k7_setfam_1 @ X3 @ X2)) = (X2))
% 0.20/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.20/0.46      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.46          | ~ (r1_tarski @ (k7_setfam_1 @ sk_A @ X0) @ sk_C)
% 0.20/0.46          | (r1_tarski @ X0 @ (k7_setfam_1 @ sk_A @ sk_C)))),
% 0.20/0.46      inference('demod', [status(thm)], ['26', '29'])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))
% 0.20/0.46        | ~ (r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['21', '30'])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      (((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C))
% 0.20/0.46         <= (((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('33', plain,
% 0.20/0.46      (((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C)) | 
% 0.20/0.46       ((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C)))),
% 0.20/0.46      inference('split', [status(esa)], ['3'])).
% 0.20/0.46  thf('34', plain, (((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['2', '18', '33'])).
% 0.20/0.46  thf('35', plain, ((r1_tarski @ (k7_setfam_1 @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['32', '34'])).
% 0.20/0.46  thf('36', plain, ((r1_tarski @ sk_B @ (k7_setfam_1 @ sk_A @ sk_C))),
% 0.20/0.46      inference('demod', [status(thm)], ['31', '35'])).
% 0.20/0.46  thf('37', plain, ($false), inference('demod', [status(thm)], ['20', '36'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
