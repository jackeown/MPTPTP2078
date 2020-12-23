%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LZN7NJgs0I

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:51 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 173 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :  693 (3016 expanded)
%              Number of equality atoms :   41 ( 174 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X14 @ ( k2_pre_topc @ X14 @ X13 ) ) @ ( k2_tops_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t71_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X12 @ ( k1_tops_1 @ X12 @ X11 ) ) @ ( k2_tops_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t71_tops_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v6_tops_1 @ X5 @ X6 )
      | ( X5
        = ( k1_tops_1 @ X6 @ ( k2_pre_topc @ X6 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','20'])).

thf('22',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( k2_tops_1 @ X8 @ X7 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X8 ) @ ( k2_pre_topc @ X8 @ X7 ) @ ( k1_tops_1 @ X8 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k1_tops_1 @ X9 @ ( k1_tops_1 @ X9 @ X10 ) )
        = ( k1_tops_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('30',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('32',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','38'])).

thf('40',plain,
    ( $false
   <= ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','21'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('46',plain,(
    ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['40','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LZN7NJgs0I
% 0.13/0.37  % Computer   : n020.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:40:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 55 iterations in 0.034s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.52  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.34/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.34/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.34/0.52  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.34/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.34/0.52  thf(t104_tops_1, conjecture,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( l1_pre_topc @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( ( v6_tops_1 @ B @ A ) =>
% 0.34/0.52             ( ( ( k2_tops_1 @ A @ B ) =
% 0.34/0.52                 ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) & 
% 0.34/0.52               ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.34/0.52                 ( k7_subset_1 @
% 0.34/0.52                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i]:
% 0.34/0.52        ( ( l1_pre_topc @ A ) =>
% 0.34/0.52          ( ![B:$i]:
% 0.34/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52              ( ( v6_tops_1 @ B @ A ) =>
% 0.34/0.52                ( ( ( k2_tops_1 @ A @ B ) =
% 0.34/0.52                    ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) & 
% 0.34/0.52                  ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.34/0.52                    ( k7_subset_1 @
% 0.34/0.52                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t104_tops_1])).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(t72_tops_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( l1_pre_topc @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( r1_tarski @
% 0.34/0.52             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.34/0.52             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (![X13 : $i, X14 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.34/0.52          | (r1_tarski @ (k2_tops_1 @ X14 @ (k2_pre_topc @ X14 @ X13)) @ 
% 0.34/0.52             (k2_tops_1 @ X14 @ X13))
% 0.34/0.52          | ~ (l1_pre_topc @ X14))),
% 0.34/0.52      inference('cnf', [status(esa)], [t72_tops_1])).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.52        | (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.34/0.52           (k2_tops_1 @ sk_A @ sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.52  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.34/0.52        (k2_tops_1 @ sk_A @ sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.34/0.52  thf(d10_xboole_0, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      (![X0 : $i, X2 : $i]:
% 0.34/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.34/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      ((~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.34/0.52           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.34/0.52        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52            = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(dt_k2_pre_topc, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.34/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.52       ( m1_subset_1 @
% 0.34/0.52         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (![X3 : $i, X4 : $i]:
% 0.34/0.52         (~ (l1_pre_topc @ X3)
% 0.34/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.34/0.52          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.34/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.34/0.52      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.34/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.34/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.34/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.34/0.52  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.34/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.34/0.52  thf(t71_tops_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( l1_pre_topc @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( r1_tarski @
% 0.34/0.52             ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (![X11 : $i, X12 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.34/0.52          | (r1_tarski @ (k2_tops_1 @ X12 @ (k1_tops_1 @ X12 @ X11)) @ 
% 0.34/0.52             (k2_tops_1 @ X12 @ X11))
% 0.34/0.52          | ~ (l1_pre_topc @ X12))),
% 0.34/0.52      inference('cnf', [status(esa)], [t71_tops_1])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.52        | (r1_tarski @ 
% 0.34/0.52           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 0.34/0.52           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.52  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('15', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(d8_tops_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( l1_pre_topc @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( ( v6_tops_1 @ B @ A ) <=>
% 0.34/0.52             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X5 : $i, X6 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.34/0.52          | ~ (v6_tops_1 @ X5 @ X6)
% 0.34/0.52          | ((X5) = (k1_tops_1 @ X6 @ (k2_pre_topc @ X6 @ X5)))
% 0.34/0.52          | ~ (l1_pre_topc @ X6))),
% 0.34/0.52      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.34/0.52  thf('17', plain,
% 0.34/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.52        | ((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.34/0.52        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.34/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.52  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('19', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('20', plain,
% 0.34/0.52      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.34/0.52      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.34/0.52  thf('21', plain,
% 0.34/0.52      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.34/0.52        (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.34/0.52      inference('demod', [status(thm)], ['13', '14', '20'])).
% 0.34/0.52  thf('22', plain,
% 0.34/0.52      (((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.34/0.52      inference('demod', [status(thm)], ['6', '21'])).
% 0.34/0.52  thf('23', plain,
% 0.34/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(l78_tops_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( l1_pre_topc @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.34/0.52           ( ( k2_tops_1 @ A @ B ) =
% 0.34/0.52             ( k7_subset_1 @
% 0.34/0.52               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.34/0.52               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      (![X7 : $i, X8 : $i]:
% 0.34/0.52         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.34/0.52          | ((k2_tops_1 @ X8 @ X7)
% 0.34/0.52              = (k7_subset_1 @ (u1_struct_0 @ X8) @ (k2_pre_topc @ X8 @ X7) @ 
% 0.34/0.52                 (k1_tops_1 @ X8 @ X7)))
% 0.34/0.52          | ~ (l1_pre_topc @ X8))),
% 0.34/0.52      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.34/0.52        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.52               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.34/0.52  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      (((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.34/0.52            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.34/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.34/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.34/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.34/0.52  thf(projectivity_k1_tops_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.34/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.34/0.52       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.34/0.52  thf('29', plain,
% 0.34/0.52      (![X9 : $i, X10 : $i]:
% 0.34/0.52         (~ (l1_pre_topc @ X9)
% 0.34/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.34/0.52          | ((k1_tops_1 @ X9 @ (k1_tops_1 @ X9 @ X10)) = (k1_tops_1 @ X9 @ X10)))),
% 0.34/0.52      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.34/0.52  thf('30', plain,
% 0.34/0.52      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.34/0.52          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.34/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.34/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.34/0.52      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.34/0.52      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.34/0.52  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('34', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      (((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.34/0.52            sk_B))),
% 0.34/0.52      inference('demod', [status(thm)], ['27', '34'])).
% 0.34/0.52  thf('36', plain,
% 0.34/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52          != (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.34/0.52        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.34/0.52            != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.52                (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('37', plain,
% 0.34/0.52      ((((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.34/0.52          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.52              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.34/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.52                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['36'])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      ((((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.34/0.52          != (k2_tops_1 @ sk_A @ sk_B)))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.34/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.52                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['35', '37'])).
% 0.34/0.52  thf('39', plain,
% 0.34/0.52      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.34/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.52                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['22', '38'])).
% 0.34/0.52  thf('40', plain,
% 0.34/0.52      (($false)
% 0.34/0.52         <= (~
% 0.34/0.52             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.34/0.52                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.52                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.34/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.34/0.52  thf('41', plain,
% 0.34/0.52      (((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.34/0.52      inference('demod', [status(thm)], ['6', '21'])).
% 0.34/0.52  thf('42', plain,
% 0.34/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52          != (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52                = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.34/0.52      inference('split', [status(esa)], ['36'])).
% 0.34/0.52  thf('43', plain,
% 0.34/0.52      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52                = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.34/0.52  thf('44', plain,
% 0.34/0.52      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52          = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.34/0.52      inference('simplify', [status(thm)], ['43'])).
% 0.34/0.52  thf('45', plain,
% 0.34/0.52      (~
% 0.34/0.52       (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.34/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.52             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.34/0.52       ~
% 0.34/0.52       (((k2_tops_1 @ sk_A @ sk_B)
% 0.34/0.52          = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['36'])).
% 0.34/0.52  thf('46', plain,
% 0.34/0.52      (~
% 0.34/0.52       (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.34/0.52          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.34/0.52             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.34/0.52  thf('47', plain, ($false),
% 0.34/0.52      inference('simpl_trail', [status(thm)], ['40', '46'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
