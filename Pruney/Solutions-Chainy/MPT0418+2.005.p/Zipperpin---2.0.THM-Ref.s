%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y2OexTZCDr

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:15 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 146 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  547 (1912 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(t49_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
            <=> ( r2_hidden @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_setfam_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
   <= ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('8',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('10',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( X0
       != ( k7_setfam_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X1 @ X3 ) @ X2 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k7_setfam_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X1 @ X3 ) @ X2 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_setfam_1 @ X7 @ ( k7_setfam_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('18',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['4','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('27',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','23','27'])).

thf('29',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['26','28'])).

thf('30',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( X0
       != ( k7_setfam_1 @ X1 @ X2 ) )
      | ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X1 @ X3 ) @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X1 @ X3 ) @ X2 )
      | ( r2_hidden @ X3 @ ( k7_setfam_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('36',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['25','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y2OexTZCDr
% 0.13/0.37  % Computer   : n003.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:33:12 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 34 iterations in 0.022s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.50  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.23/0.50  thf(t49_setfam_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50       ( ![C:$i]:
% 0.23/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.23/0.50             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i]:
% 0.23/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50          ( ![C:$i]:
% 0.23/0.50            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50              ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.23/0.50                ( r2_hidden @ C @ B ) ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t49_setfam_1])).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.23/0.50        | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.23/0.50             (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      ((~ (r2_hidden @ sk_C @ sk_B)) <= (~ ((r2_hidden @ sk_C @ sk_B)))),
% 0.23/0.50      inference('split', [status(esa)], ['0'])).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (~ ((r2_hidden @ sk_C @ sk_B)) | 
% 0.23/0.50       ~
% 0.23/0.50       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.23/0.50      inference('split', [status(esa)], ['0'])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (((r2_hidden @ sk_C @ sk_B)
% 0.23/0.50        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.23/0.50           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (((r2_hidden @ sk_C @ sk_B)) <= (((r2_hidden @ sk_C @ sk_B)))),
% 0.23/0.50      inference('split', [status(esa)], ['3'])).
% 0.23/0.50  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(dt_k7_setfam_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50       ( m1_subset_1 @
% 0.23/0.50         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X4 : $i, X5 : $i]:
% 0.23/0.50         ((m1_subset_1 @ (k7_setfam_1 @ X4 @ X5) @ 
% 0.23/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4)))
% 0.23/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.23/0.50      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.23/0.50  thf('8', plain,
% 0.23/0.50      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X4 : $i, X5 : $i]:
% 0.23/0.50         ((m1_subset_1 @ (k7_setfam_1 @ X4 @ X5) @ 
% 0.23/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4)))
% 0.23/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.23/0.50      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.50  thf(d8_setfam_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50       ( ![C:$i]:
% 0.23/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.23/0.50             ( ![D:$i]:
% 0.23/0.50               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.50                 ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.50                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.23/0.50          | ((X0) != (k7_setfam_1 @ X1 @ X2))
% 0.23/0.50          | (r2_hidden @ (k3_subset_1 @ X1 @ X3) @ X2)
% 0.23/0.50          | ~ (r2_hidden @ X3 @ X0)
% 0.23/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X1))
% 0.23/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.23/0.50      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.23/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X1))
% 0.23/0.50          | ~ (r2_hidden @ X3 @ (k7_setfam_1 @ X1 @ X2))
% 0.23/0.50          | (r2_hidden @ (k3_subset_1 @ X1 @ X3) @ X2)
% 0.23/0.50          | ~ (m1_subset_1 @ (k7_setfam_1 @ X1 @ X2) @ 
% 0.23/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.23/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.23/0.50          | ~ (r2_hidden @ X0 @ 
% 0.23/0.50               (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.23/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.50          | ~ (m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.23/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['10', '12'])).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.23/0.50          | ~ (r2_hidden @ X0 @ 
% 0.23/0.50               (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.23/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(involutiveness_k7_setfam_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.23/0.50       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (![X6 : $i, X7 : $i]:
% 0.23/0.50         (((k7_setfam_1 @ X7 @ (k7_setfam_1 @ X7 @ X6)) = (X6))
% 0.23/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.23/0.50      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.23/0.50          | ~ (r2_hidden @ X0 @ sk_B)
% 0.23/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('demod', [status(thm)], ['15', '18'])).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.23/0.50        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.23/0.50           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['5', '19'])).
% 0.23/0.50  thf('21', plain,
% 0.23/0.50      (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.23/0.50         <= (((r2_hidden @ sk_C @ sk_B)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['4', '20'])).
% 0.23/0.50  thf('22', plain,
% 0.23/0.50      ((~ (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.23/0.50           (k7_setfam_1 @ sk_A @ sk_B)))
% 0.23/0.50         <= (~
% 0.23/0.50             ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.23/0.50               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.23/0.50      inference('split', [status(esa)], ['0'])).
% 0.23/0.50  thf('23', plain,
% 0.23/0.50      (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B))) | 
% 0.23/0.50       ~ ((r2_hidden @ sk_C @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.50  thf('24', plain, (~ ((r2_hidden @ sk_C @ sk_B))),
% 0.23/0.50      inference('sat_resolution*', [status(thm)], ['2', '23'])).
% 0.23/0.50  thf('25', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 0.23/0.50      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 0.23/0.50  thf('26', plain,
% 0.23/0.50      (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.23/0.50         <= (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.23/0.50               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.23/0.50      inference('split', [status(esa)], ['3'])).
% 0.23/0.50  thf('27', plain,
% 0.23/0.50      (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B))) | 
% 0.23/0.50       ((r2_hidden @ sk_C @ sk_B))),
% 0.23/0.50      inference('split', [status(esa)], ['3'])).
% 0.23/0.50  thf('28', plain,
% 0.23/0.50      (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.23/0.50      inference('sat_resolution*', [status(thm)], ['2', '23', '27'])).
% 0.23/0.50  thf('29', plain,
% 0.23/0.50      ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B))),
% 0.23/0.50      inference('simpl_trail', [status(thm)], ['26', '28'])).
% 0.23/0.50  thf('30', plain,
% 0.23/0.50      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.50  thf('31', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.23/0.50          | ((X0) != (k7_setfam_1 @ X1 @ X2))
% 0.23/0.50          | (r2_hidden @ X3 @ X0)
% 0.23/0.50          | ~ (r2_hidden @ (k3_subset_1 @ X1 @ X3) @ X2)
% 0.23/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X1))
% 0.23/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.23/0.50      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.23/0.50  thf('32', plain,
% 0.23/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1)))
% 0.23/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X1))
% 0.23/0.50          | ~ (r2_hidden @ (k3_subset_1 @ X1 @ X3) @ X2)
% 0.23/0.50          | (r2_hidden @ X3 @ (k7_setfam_1 @ X1 @ X2))
% 0.23/0.50          | ~ (m1_subset_1 @ (k7_setfam_1 @ X1 @ X2) @ 
% 0.23/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.23/0.50      inference('simplify', [status(thm)], ['31'])).
% 0.23/0.50  thf('33', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.23/0.50          | (r2_hidden @ X0 @ 
% 0.23/0.50             (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.23/0.50          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.23/0.50               (k7_setfam_1 @ sk_A @ sk_B))
% 0.23/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.50          | ~ (m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.23/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['30', '32'])).
% 0.23/0.50  thf('34', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('35', plain,
% 0.23/0.50      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.50  thf('36', plain,
% 0.23/0.50      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf('37', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((r2_hidden @ X0 @ sk_B)
% 0.23/0.50          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.23/0.50               (k7_setfam_1 @ sk_A @ sk_B))
% 0.23/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.50      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.23/0.50  thf('38', plain,
% 0.23/0.50      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.50        | (r2_hidden @ sk_C @ sk_B))),
% 0.23/0.50      inference('sup-', [status(thm)], ['29', '37'])).
% 0.23/0.50  thf('39', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('40', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.23/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.23/0.50  thf('41', plain, ($false), inference('demod', [status(thm)], ['25', '40'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
