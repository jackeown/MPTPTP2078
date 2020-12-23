%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E2FKo27Rye

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:48 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 138 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  576 (1580 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t103_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v5_tops_1 @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v5_tops_1 @ X14 @ X15 )
      | ( X14
        = ( k2_pre_topc @ X15 @ ( k1_tops_1 @ X15 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_pre_topc @ X21 @ X20 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ ( k2_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('26',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X23 @ ( k2_pre_topc @ X23 @ X22 ) ) @ ( k2_tops_1 @ X23 @ X22 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('39',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['27','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['7','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E2FKo27Rye
% 0.15/0.38  % Computer   : n008.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 12:08:45 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 1.32/1.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.32/1.50  % Solved by: fo/fo7.sh
% 1.32/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.32/1.50  % done 544 iterations in 1.000s
% 1.32/1.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.32/1.50  % SZS output start Refutation
% 1.32/1.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.32/1.50  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.32/1.50  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.32/1.50  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.32/1.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.32/1.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.32/1.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.32/1.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.32/1.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.32/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.32/1.50  thf(sk_B_type, type, sk_B: $i).
% 1.32/1.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.32/1.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.32/1.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.32/1.50  thf(t103_tops_1, conjecture,
% 1.32/1.50    (![A:$i]:
% 1.32/1.50     ( ( l1_pre_topc @ A ) =>
% 1.32/1.50       ( ![B:$i]:
% 1.32/1.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.50           ( ( v5_tops_1 @ B @ A ) =>
% 1.32/1.50             ( r1_tarski @
% 1.32/1.50               ( k2_tops_1 @ A @ B ) @ 
% 1.32/1.50               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.32/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.32/1.50    (~( ![A:$i]:
% 1.32/1.50        ( ( l1_pre_topc @ A ) =>
% 1.32/1.50          ( ![B:$i]:
% 1.32/1.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.50              ( ( v5_tops_1 @ B @ A ) =>
% 1.32/1.50                ( r1_tarski @
% 1.32/1.50                  ( k2_tops_1 @ A @ B ) @ 
% 1.32/1.50                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.32/1.50    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 1.32/1.50  thf('0', plain,
% 1.32/1.50      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.32/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.50  thf('1', plain,
% 1.32/1.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.50  thf(d7_tops_1, axiom,
% 1.32/1.50    (![A:$i]:
% 1.32/1.50     ( ( l1_pre_topc @ A ) =>
% 1.32/1.50       ( ![B:$i]:
% 1.32/1.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.50           ( ( v5_tops_1 @ B @ A ) <=>
% 1.32/1.50             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.32/1.50  thf('2', plain,
% 1.32/1.50      (![X14 : $i, X15 : $i]:
% 1.32/1.50         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.32/1.50          | ~ (v5_tops_1 @ X14 @ X15)
% 1.32/1.50          | ((X14) = (k2_pre_topc @ X15 @ (k1_tops_1 @ X15 @ X14)))
% 1.32/1.50          | ~ (l1_pre_topc @ X15))),
% 1.32/1.50      inference('cnf', [status(esa)], [d7_tops_1])).
% 1.32/1.50  thf('3', plain,
% 1.32/1.50      ((~ (l1_pre_topc @ sk_A)
% 1.32/1.50        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.32/1.50        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 1.32/1.50      inference('sup-', [status(thm)], ['1', '2'])).
% 1.32/1.50  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.50  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.32/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.50  thf('6', plain,
% 1.32/1.50      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.32/1.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.32/1.50  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.32/1.50      inference('demod', [status(thm)], ['0', '6'])).
% 1.32/1.50  thf('8', plain,
% 1.32/1.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.50  thf(dt_k1_tops_1, axiom,
% 1.32/1.50    (![A:$i,B:$i]:
% 1.32/1.50     ( ( ( l1_pre_topc @ A ) & 
% 1.32/1.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.32/1.50       ( m1_subset_1 @
% 1.32/1.50         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.32/1.50  thf('9', plain,
% 1.32/1.50      (![X16 : $i, X17 : $i]:
% 1.32/1.50         (~ (l1_pre_topc @ X16)
% 1.32/1.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.32/1.50          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 1.32/1.50             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 1.32/1.50      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.32/1.50  thf('10', plain,
% 1.32/1.50      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.50        | ~ (l1_pre_topc @ sk_A))),
% 1.32/1.50      inference('sup-', [status(thm)], ['8', '9'])).
% 1.32/1.50  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.50  thf('12', plain,
% 1.32/1.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.50      inference('demod', [status(thm)], ['10', '11'])).
% 1.32/1.50  thf(dt_k2_tops_1, axiom,
% 1.32/1.50    (![A:$i,B:$i]:
% 1.32/1.50     ( ( ( l1_pre_topc @ A ) & 
% 1.32/1.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.32/1.50       ( m1_subset_1 @
% 1.32/1.50         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.32/1.50  thf('13', plain,
% 1.32/1.50      (![X18 : $i, X19 : $i]:
% 1.32/1.50         (~ (l1_pre_topc @ X18)
% 1.32/1.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.32/1.50          | (m1_subset_1 @ (k2_tops_1 @ X18 @ X19) @ 
% 1.32/1.50             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 1.32/1.50      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.32/1.50  thf('14', plain,
% 1.32/1.50      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.32/1.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.32/1.50        | ~ (l1_pre_topc @ sk_A))),
% 1.32/1.50      inference('sup-', [status(thm)], ['12', '13'])).
% 1.32/1.50  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.50  thf('16', plain,
% 1.32/1.50      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.32/1.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.50      inference('demod', [status(thm)], ['14', '15'])).
% 1.32/1.50  thf('17', plain,
% 1.32/1.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.50      inference('demod', [status(thm)], ['10', '11'])).
% 1.32/1.50  thf(redefinition_k4_subset_1, axiom,
% 1.32/1.50    (![A:$i,B:$i,C:$i]:
% 1.32/1.50     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.32/1.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.32/1.50       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.32/1.50  thf('18', plain,
% 1.32/1.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.32/1.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.32/1.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 1.32/1.50          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 1.32/1.50      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.32/1.50  thf('19', plain,
% 1.32/1.50      (![X0 : $i]:
% 1.32/1.50         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.32/1.50            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 1.32/1.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.32/1.50      inference('sup-', [status(thm)], ['17', '18'])).
% 1.32/1.50  thf('20', plain,
% 1.32/1.50      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50         (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.32/1.50         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.32/1.50      inference('sup-', [status(thm)], ['16', '19'])).
% 1.32/1.50  thf('21', plain,
% 1.32/1.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.50      inference('demod', [status(thm)], ['10', '11'])).
% 1.32/1.50  thf(t65_tops_1, axiom,
% 1.32/1.50    (![A:$i]:
% 1.32/1.50     ( ( l1_pre_topc @ A ) =>
% 1.32/1.50       ( ![B:$i]:
% 1.32/1.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.50           ( ( k2_pre_topc @ A @ B ) =
% 1.32/1.50             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.32/1.50  thf('22', plain,
% 1.32/1.50      (![X20 : $i, X21 : $i]:
% 1.32/1.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.32/1.50          | ((k2_pre_topc @ X21 @ X20)
% 1.32/1.50              = (k4_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 1.32/1.50                 (k2_tops_1 @ X21 @ X20)))
% 1.32/1.50          | ~ (l1_pre_topc @ X21))),
% 1.32/1.50      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.32/1.50  thf('23', plain,
% 1.32/1.50      ((~ (l1_pre_topc @ sk_A)
% 1.32/1.50        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.32/1.50            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.32/1.50               (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.32/1.50      inference('sup-', [status(thm)], ['21', '22'])).
% 1.32/1.50  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.50  thf('25', plain,
% 1.32/1.50      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.32/1.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.32/1.50  thf('26', plain,
% 1.32/1.50      (((sk_B)
% 1.32/1.50         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.32/1.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.32/1.50  thf('27', plain,
% 1.32/1.50      (((sk_B)
% 1.32/1.50         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.32/1.50      inference('sup+', [status(thm)], ['20', '26'])).
% 1.32/1.50  thf(d10_xboole_0, axiom,
% 1.32/1.50    (![A:$i,B:$i]:
% 1.32/1.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.32/1.50  thf('28', plain,
% 1.32/1.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.32/1.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.32/1.50  thf('29', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.32/1.50      inference('simplify', [status(thm)], ['28'])).
% 1.32/1.50  thf(t44_xboole_1, axiom,
% 1.32/1.50    (![A:$i,B:$i,C:$i]:
% 1.32/1.50     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.32/1.50       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.32/1.50  thf('30', plain,
% 1.32/1.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.32/1.50         ((r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 1.32/1.50          | ~ (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 1.32/1.50      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.32/1.50  thf('31', plain,
% 1.32/1.50      (![X0 : $i, X1 : $i]:
% 1.32/1.50         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.32/1.50      inference('sup-', [status(thm)], ['29', '30'])).
% 1.32/1.50  thf(t39_xboole_1, axiom,
% 1.32/1.50    (![A:$i,B:$i]:
% 1.32/1.50     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.32/1.50  thf('32', plain,
% 1.32/1.50      (![X6 : $i, X7 : $i]:
% 1.32/1.50         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 1.32/1.50           = (k2_xboole_0 @ X6 @ X7))),
% 1.32/1.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.32/1.50  thf('33', plain,
% 1.32/1.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 1.32/1.50      inference('demod', [status(thm)], ['31', '32'])).
% 1.32/1.50  thf('34', plain,
% 1.32/1.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.32/1.50      inference('demod', [status(thm)], ['10', '11'])).
% 1.32/1.50  thf(t72_tops_1, axiom,
% 1.32/1.50    (![A:$i]:
% 1.32/1.50     ( ( l1_pre_topc @ A ) =>
% 1.32/1.50       ( ![B:$i]:
% 1.32/1.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.32/1.50           ( r1_tarski @
% 1.32/1.50             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 1.32/1.50             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 1.32/1.50  thf('35', plain,
% 1.32/1.50      (![X22 : $i, X23 : $i]:
% 1.32/1.50         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.32/1.50          | (r1_tarski @ (k2_tops_1 @ X23 @ (k2_pre_topc @ X23 @ X22)) @ 
% 1.32/1.50             (k2_tops_1 @ X23 @ X22))
% 1.32/1.50          | ~ (l1_pre_topc @ X23))),
% 1.32/1.50      inference('cnf', [status(esa)], [t72_tops_1])).
% 1.32/1.50  thf('36', plain,
% 1.32/1.50      ((~ (l1_pre_topc @ sk_A)
% 1.32/1.50        | (r1_tarski @ 
% 1.32/1.50           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 1.32/1.50           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.32/1.50      inference('sup-', [status(thm)], ['34', '35'])).
% 1.32/1.50  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.32/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.32/1.50  thf('38', plain,
% 1.32/1.50      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.32/1.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.32/1.50  thf('39', plain,
% 1.32/1.50      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.32/1.50      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.32/1.50  thf(t1_xboole_1, axiom,
% 1.32/1.50    (![A:$i,B:$i,C:$i]:
% 1.32/1.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.32/1.50       ( r1_tarski @ A @ C ) ))).
% 1.32/1.50  thf('40', plain,
% 1.32/1.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.32/1.50         (~ (r1_tarski @ X3 @ X4)
% 1.32/1.50          | ~ (r1_tarski @ X4 @ X5)
% 1.32/1.50          | (r1_tarski @ X3 @ X5))),
% 1.32/1.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.32/1.50  thf('41', plain,
% 1.32/1.50      (![X0 : $i]:
% 1.32/1.50         ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.32/1.50          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 1.32/1.50      inference('sup-', [status(thm)], ['39', '40'])).
% 1.32/1.50  thf('42', plain,
% 1.32/1.50      (![X0 : $i]:
% 1.32/1.50         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.32/1.50          (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.32/1.50      inference('sup-', [status(thm)], ['33', '41'])).
% 1.32/1.50  thf('43', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.32/1.50      inference('sup+', [status(thm)], ['27', '42'])).
% 1.32/1.50  thf('44', plain, ($false), inference('demod', [status(thm)], ['7', '43'])).
% 1.32/1.50  
% 1.32/1.50  % SZS output end Refutation
% 1.32/1.50  
% 1.32/1.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
