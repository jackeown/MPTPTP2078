%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.40rd9rNfRb

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 163 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  620 (2932 expanded)
%              Number of equality atoms :   41 ( 179 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t104_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
           => ( ( ( k2_tops_1 @ A @ B )
                = ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
              & ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v6_tops_1 @ B @ A )
             => ( ( ( k2_tops_1 @ A @ B )
                  = ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) )
                & ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) )
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t104_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k2_tops_1 @ X7 @ X6 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k2_pre_topc @ X7 @ X6 ) @ ( k1_tops_1 @ X7 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( ( k2_pre_topc @ X2 @ ( k2_pre_topc @ X2 @ X3 ) )
        = ( k2_pre_topc @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('10',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( B
              = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v6_tops_1 @ X4 @ X5 )
      | ( X4
        = ( k1_tops_1 @ X5 @ ( k2_pre_topc @ X5 @ X4 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','12','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k2_tops_1 @ X7 @ X6 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k2_pre_topc @ X7 @ X6 ) @ ( k1_tops_1 @ X7 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( k1_tops_1 @ X8 @ ( k1_tops_1 @ X8 @ X9 ) )
        = ( k1_tops_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('27',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('29',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','31'])).

thf('33',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','12','18'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('41',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['35','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.40rd9rNfRb
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:04:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 33 iterations in 0.018s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.49  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.49  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(t104_tops_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( v6_tops_1 @ B @ A ) =>
% 0.22/0.49             ( ( ( k2_tops_1 @ A @ B ) =
% 0.22/0.49                 ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) & 
% 0.22/0.49               ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.22/0.49                 ( k7_subset_1 @
% 0.22/0.49                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( l1_pre_topc @ A ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49              ( ( v6_tops_1 @ B @ A ) =>
% 0.22/0.49                ( ( ( k2_tops_1 @ A @ B ) =
% 0.22/0.49                    ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) & 
% 0.22/0.49                  ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.22/0.49                    ( k7_subset_1 @
% 0.22/0.49                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t104_tops_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k2_pre_topc, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.49       ( m1_subset_1 @
% 0.22/0.49         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X0)
% 0.22/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.49          | (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(l78_tops_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( k2_tops_1 @ A @ B ) =
% 0.22/0.49             ( k7_subset_1 @
% 0.22/0.49               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.22/0.49               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.49          | ((k2_tops_1 @ X7 @ X6)
% 0.22/0.49              = (k7_subset_1 @ (u1_struct_0 @ X7) @ (k2_pre_topc @ X7 @ X6) @ 
% 0.22/0.49                 (k1_tops_1 @ X7 @ X6)))
% 0.22/0.49          | ~ (l1_pre_topc @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49               (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.49               (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(projectivity_k2_pre_topc, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.49       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.22/0.49         ( k2_pre_topc @ A @ B ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X2)
% 0.22/0.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.22/0.49          | ((k2_pre_topc @ X2 @ (k2_pre_topc @ X2 @ X3))
% 0.22/0.49              = (k2_pre_topc @ X2 @ X3)))),
% 0.22/0.49      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49          = (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d8_tops_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49           ( ( v6_tops_1 @ B @ A ) <=>
% 0.22/0.49             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.22/0.49          | ~ (v6_tops_1 @ X4 @ X5)
% 0.22/0.49          | ((X4) = (k1_tops_1 @ X5 @ (k2_pre_topc @ X5 @ X4)))
% 0.22/0.49          | ~ (l1_pre_topc @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | ((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.22/0.49        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('17', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.49            sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '7', '12', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.49          | ((k2_tops_1 @ X7 @ X6)
% 0.22/0.49              = (k7_subset_1 @ (u1_struct_0 @ X7) @ (k2_pre_topc @ X7 @ X6) @ 
% 0.22/0.49                 (k1_tops_1 @ X7 @ X6)))
% 0.22/0.49          | ~ (l1_pre_topc @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.49            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.49         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.49            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(projectivity_k1_tops_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.49       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X8)
% 0.22/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.49          | ((k1_tops_1 @ X8 @ (k1_tops_1 @ X8 @ X9)) = (k1_tops_1 @ X8 @ X9)))),
% 0.22/0.49      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.22/0.49          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.22/0.49  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('31', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.49         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.49            sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['24', '31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.49         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['19', '32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.49          != (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.22/0.49        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49            != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49                (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.49          != (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.49                = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.22/0.49      inference('split', [status(esa)], ['34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.49            sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '7', '12', '18'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      ((((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.22/0.49      inference('split', [status(esa)], ['34'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49          != (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.22/0.49         <= (~
% 0.22/0.49             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      ((((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.49          = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))) | 
% 0.22/0.49       ~
% 0.22/0.49       (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.22/0.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.49             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['34'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (~
% 0.22/0.49       (((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.49          = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (((k2_tops_1 @ sk_A @ sk_B)
% 0.22/0.49         != (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['35', '41'])).
% 0.22/0.49  thf('43', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['33', '42'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
