%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j48YpqSYfQ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  92 expanded)
%              Number of leaves         :   13 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  533 (1173 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('6',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ( X4
       != ( k7_setfam_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X5 @ X7 ) @ X6 )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ X7 @ ( k7_setfam_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X5 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('15',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','15','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
   <= ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('23',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('25',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ( X4
       != ( k7_setfam_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X5 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X5 @ X7 ) @ X6 )
      | ( r2_hidden @ X7 @ ( k7_setfam_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','21','22','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j48YpqSYfQ
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:09:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 53 iterations in 0.021s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.21/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.47  thf(t49_setfam_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.21/0.47             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47          ( ![C:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47              ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.21/0.47                ( r2_hidden @ C @ B ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t49_setfam_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.21/0.47        | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47             (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (~ ((r2_hidden @ sk_C @ sk_B)) | 
% 0.21/0.47       ~
% 0.21/0.47       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (((r2_hidden @ sk_C @ sk_B)
% 0.21/0.47        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.21/0.47         <= (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k7_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( m1_subset_1 @
% 0.21/0.47         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k7_setfam_1 @ X8 @ X9) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8)))
% 0.21/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf(d8_setfam_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.47           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.21/0.47             ( ![D:$i]:
% 0.21/0.47               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47                 ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.47                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5)))
% 0.21/0.47          | ((X4) != (k7_setfam_1 @ X5 @ X6))
% 0.21/0.47          | (r2_hidden @ (k3_subset_1 @ X5 @ X7) @ X6)
% 0.21/0.47          | ~ (r2_hidden @ X7 @ X4)
% 0.21/0.47          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5))
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.47      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5)))
% 0.21/0.47          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5))
% 0.21/0.47          | ~ (r2_hidden @ X7 @ (k7_setfam_1 @ X5 @ X6))
% 0.21/0.47          | (r2_hidden @ (k3_subset_1 @ X5 @ X7) @ X6)
% 0.21/0.47          | ~ (m1_subset_1 @ (k7_setfam_1 @ X5 @ X6) @ 
% 0.21/0.47               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.47          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.21/0.47          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.47         | (r2_hidden @ (k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) @ 
% 0.21/0.47            sk_B)))
% 0.21/0.47         <= (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '11'])).
% 0.21/0.47  thf('13', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k3_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.21/0.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.47      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (((r2_hidden @ sk_C @ sk_B))
% 0.21/0.47         <= (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '15', '18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_C @ sk_B)) <= (~ ((r2_hidden @ sk_C @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (((r2_hidden @ sk_C @ sk_B)) | 
% 0.21/0.47       ~
% 0.21/0.47       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (((r2_hidden @ sk_C @ sk_B)) | 
% 0.21/0.47       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (((r2_hidden @ sk_C @ sk_B)) <= (((r2_hidden @ sk_C @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['2'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.21/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5)))
% 0.21/0.47          | ((X4) != (k7_setfam_1 @ X5 @ X6))
% 0.21/0.47          | (r2_hidden @ X7 @ X4)
% 0.21/0.47          | ~ (r2_hidden @ (k3_subset_1 @ X5 @ X7) @ X6)
% 0.21/0.47          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5))
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.47      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5)))
% 0.21/0.47          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5))
% 0.21/0.47          | ~ (r2_hidden @ (k3_subset_1 @ X5 @ X7) @ X6)
% 0.21/0.47          | (r2_hidden @ X7 @ (k7_setfam_1 @ X5 @ X6))
% 0.21/0.47          | ~ (m1_subset_1 @ (k7_setfam_1 @ X5 @ X6) @ 
% 0.21/0.47               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.21/0.47          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.47          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.21/0.47          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.21/0.47        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.47        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['24', '30'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      ((~ (r2_hidden @ sk_C @ sk_B)
% 0.21/0.47        | (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47           (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.21/0.47         <= (((r2_hidden @ sk_C @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '33'])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      ((~ (r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47           (k7_setfam_1 @ sk_A @ sk_B)))
% 0.21/0.47         <= (~
% 0.21/0.47             ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47               (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (~ ((r2_hidden @ sk_C @ sk_B)) | 
% 0.21/0.47       ((r2_hidden @ (k3_subset_1 @ sk_A @ sk_C) @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.47  thf('37', plain, ($false),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['1', '21', '22', '36'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
