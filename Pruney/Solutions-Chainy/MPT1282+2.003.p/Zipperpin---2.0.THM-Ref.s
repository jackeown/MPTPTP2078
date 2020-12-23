%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0czg9diHet

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 209 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  701 (3744 expanded)
%              Number of equality atoms :   47 ( 224 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t102_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
              = ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_tops_1 @ X11 @ ( k1_tops_1 @ X11 @ X10 ) )
        = ( k2_tops_1 @ X11 @ X10 ) )
      | ~ ( v5_tops_1 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t102_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v5_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( X2
       != ( k2_pre_topc @ X3 @ ( k1_tops_1 @ X3 @ X2 ) ) )
      | ( v5_tops_1 @ X2 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v5_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
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
    ( ( v5_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('20',plain,(
    v5_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('22',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7','20','21'])).

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
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k2_tops_1 @ X7 @ X6 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k2_pre_topc @ X7 @ X6 ) @ ( k1_tops_1 @ X7 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    inference(demod,[status(thm)],['2','3'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( k1_tops_1 @ X8 @ ( k1_tops_1 @ X8 @ X9 ) )
        = ( k1_tops_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('30',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('32',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

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
    inference(demod,[status(thm)],['6','7','20','21'])).

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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0czg9diHet
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:52:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 52 iterations in 0.040s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.49  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.49  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.21/0.49  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(t104_tops_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( v6_tops_1 @ B @ A ) =>
% 0.21/0.49             ( ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.49                 ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) & 
% 0.21/0.49               ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.21/0.49                 ( k7_subset_1 @
% 0.21/0.49                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( l1_pre_topc @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49              ( ( v6_tops_1 @ B @ A ) =>
% 0.21/0.49                ( ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.49                    ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) & 
% 0.21/0.49                  ( ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.21/0.49                    ( k7_subset_1 @
% 0.21/0.49                      ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t104_tops_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k2_pre_topc, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49       ( m1_subset_1 @
% 0.21/0.49         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.49          | (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(t102_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( v5_tops_1 @ B @ A ) =>
% 0.21/0.49             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.21/0.49               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.49          | ((k2_tops_1 @ X11 @ (k1_tops_1 @ X11 @ X10))
% 0.21/0.49              = (k2_tops_1 @ X11 @ X10))
% 0.21/0.49          | ~ (v5_tops_1 @ X10 @ X11)
% 0.21/0.49          | ~ (l1_pre_topc @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t102_tops_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ~ (v5_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.21/0.49            = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(d7_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( v5_tops_1 @ B @ A ) <=>
% 0.21/0.49             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.21/0.49          | ((X2) != (k2_pre_topc @ X3 @ (k1_tops_1 @ X3 @ X2)))
% 0.21/0.49          | (v5_tops_1 @ X2 @ X3)
% 0.21/0.49          | ~ (l1_pre_topc @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (v5_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.21/0.49            != (k2_pre_topc @ sk_A @ 
% 0.21/0.49                (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (((v5_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.21/0.49            != (k2_pre_topc @ sk_A @ 
% 0.21/0.49                (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d8_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( v6_tops_1 @ B @ A ) <=>
% 0.21/0.49             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.49          | ~ (v6_tops_1 @ X4 @ X5)
% 0.21/0.49          | ((X4) = (k1_tops_1 @ X5 @ (k2_pre_topc @ X5 @ X4)))
% 0.21/0.49          | ~ (l1_pre_topc @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.21/0.49        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((v5_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.49        | ((k2_pre_topc @ sk_A @ sk_B) != (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '18'])).
% 0.21/0.49  thf('20', plain, ((v5_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7', '20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l78_tops_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.49             ( k7_subset_1 @
% 0.21/0.49               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.21/0.49               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.49          | ((k2_tops_1 @ X7 @ X6)
% 0.21/0.49              = (k7_subset_1 @ (u1_struct_0 @ X7) @ (k2_pre_topc @ X7 @ X6) @ 
% 0.21/0.49                 (k1_tops_1 @ X7 @ X6)))
% 0.21/0.49          | ~ (l1_pre_topc @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.49            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf(projectivity_k1_tops_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X8)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.49          | ((k1_tops_1 @ X8 @ (k1_tops_1 @ X8 @ X9)) = (k1_tops_1 @ X8 @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.21/0.49          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.49  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.49            sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49          != (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.21/0.49        | ((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.49            != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.49          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['36'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.49          != (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (($false)
% 0.21/0.49         <= (~
% 0.21/0.49             (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7', '20', '21'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49          != (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49                = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.21/0.49      inference('split', [status(esa)], ['36'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.49         <= (~
% 0.21/0.49             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49                = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49          = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (~
% 0.21/0.49       (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.21/0.49       ~
% 0.21/0.49       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.49          = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.21/0.49      inference('split', [status(esa)], ['36'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (~
% 0.21/0.49       (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.21/0.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain, ($false),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['40', '46'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
