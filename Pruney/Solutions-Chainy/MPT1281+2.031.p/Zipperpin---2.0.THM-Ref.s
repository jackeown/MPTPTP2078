%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xYmsnCbzHo

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:48 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 126 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  559 (1362 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v5_tops_1 @ X19 @ X20 )
      | ( X19
        = ( k2_pre_topc @ X20 @ ( k1_tops_1 @ X20 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ ( k2_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k2_pre_topc @ X17 @ ( k2_pre_topc @ X17 @ X18 ) )
        = ( k2_pre_topc @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('40',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','42'])).

thf('44',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['44','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['7','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xYmsnCbzHo
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:06:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.86/1.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.86/1.05  % Solved by: fo/fo7.sh
% 0.86/1.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.05  % done 1646 iterations in 0.612s
% 0.86/1.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.86/1.05  % SZS output start Refutation
% 0.86/1.05  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.86/1.05  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.86/1.05  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.86/1.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.86/1.05  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.86/1.05  thf(sk_B_type, type, sk_B: $i).
% 0.86/1.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.86/1.05  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.86/1.05  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.86/1.05  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.86/1.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.86/1.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.86/1.05  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.05  thf(t103_tops_1, conjecture,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( l1_pre_topc @ A ) =>
% 0.86/1.05       ( ![B:$i]:
% 0.86/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.05           ( ( v5_tops_1 @ B @ A ) =>
% 0.86/1.05             ( r1_tarski @
% 0.86/1.05               ( k2_tops_1 @ A @ B ) @ 
% 0.86/1.05               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.86/1.05  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.05    (~( ![A:$i]:
% 0.86/1.05        ( ( l1_pre_topc @ A ) =>
% 0.86/1.05          ( ![B:$i]:
% 0.86/1.05            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.05              ( ( v5_tops_1 @ B @ A ) =>
% 0.86/1.05                ( r1_tarski @
% 0.86/1.05                  ( k2_tops_1 @ A @ B ) @ 
% 0.86/1.05                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.86/1.05    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.86/1.05  thf('0', plain,
% 0.86/1.05      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.86/1.05          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('1', plain,
% 0.86/1.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf(d7_tops_1, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( l1_pre_topc @ A ) =>
% 0.86/1.05       ( ![B:$i]:
% 0.86/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.05           ( ( v5_tops_1 @ B @ A ) <=>
% 0.86/1.05             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.86/1.05  thf('2', plain,
% 0.86/1.05      (![X19 : $i, X20 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.86/1.05          | ~ (v5_tops_1 @ X19 @ X20)
% 0.86/1.05          | ((X19) = (k2_pre_topc @ X20 @ (k1_tops_1 @ X20 @ X19)))
% 0.86/1.05          | ~ (l1_pre_topc @ X20))),
% 0.86/1.05      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.86/1.05  thf('3', plain,
% 0.86/1.05      ((~ (l1_pre_topc @ sk_A)
% 0.86/1.05        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.86/1.05        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['1', '2'])).
% 0.86/1.05  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('6', plain,
% 0.86/1.05      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.86/1.05      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.86/1.06  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.86/1.06      inference('demod', [status(thm)], ['0', '6'])).
% 0.86/1.06  thf('8', plain,
% 0.86/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf(dt_k2_tops_1, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( ( l1_pre_topc @ A ) & 
% 0.86/1.06         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.86/1.06       ( m1_subset_1 @
% 0.86/1.06         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.86/1.06  thf('9', plain,
% 0.86/1.06      (![X21 : $i, X22 : $i]:
% 0.86/1.06         (~ (l1_pre_topc @ X21)
% 0.86/1.06          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.86/1.06          | (m1_subset_1 @ (k2_tops_1 @ X21 @ X22) @ 
% 0.86/1.06             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 0.86/1.06      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.86/1.06  thf('10', plain,
% 0.86/1.06      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.86/1.06         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.06        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.06      inference('sup-', [status(thm)], ['8', '9'])).
% 0.86/1.06  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf('12', plain,
% 0.86/1.06      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.86/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.06      inference('demod', [status(thm)], ['10', '11'])).
% 0.86/1.06  thf('13', plain,
% 0.86/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf(redefinition_k4_subset_1, axiom,
% 0.86/1.06    (![A:$i,B:$i,C:$i]:
% 0.86/1.06     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.86/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.86/1.06       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.86/1.06  thf('14', plain,
% 0.86/1.06      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.86/1.06         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.86/1.06          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 0.86/1.06          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 0.86/1.06      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.86/1.06  thf('15', plain,
% 0.86/1.06      (![X0 : $i]:
% 0.86/1.06         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.86/1.06            = (k2_xboole_0 @ sk_B @ X0))
% 0.86/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.06      inference('sup-', [status(thm)], ['13', '14'])).
% 0.86/1.06  thf('16', plain,
% 0.86/1.06      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.86/1.06         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.86/1.06      inference('sup-', [status(thm)], ['12', '15'])).
% 0.86/1.06  thf('17', plain,
% 0.86/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf(t65_tops_1, axiom,
% 0.86/1.06    (![A:$i]:
% 0.86/1.06     ( ( l1_pre_topc @ A ) =>
% 0.86/1.06       ( ![B:$i]:
% 0.86/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.06           ( ( k2_pre_topc @ A @ B ) =
% 0.86/1.06             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.86/1.06  thf('18', plain,
% 0.86/1.06      (![X25 : $i, X26 : $i]:
% 0.86/1.06         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.86/1.06          | ((k2_pre_topc @ X26 @ X25)
% 0.86/1.06              = (k4_subset_1 @ (u1_struct_0 @ X26) @ X25 @ 
% 0.86/1.06                 (k2_tops_1 @ X26 @ X25)))
% 0.86/1.06          | ~ (l1_pre_topc @ X26))),
% 0.86/1.06      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.86/1.06  thf('19', plain,
% 0.86/1.06      ((~ (l1_pre_topc @ sk_A)
% 0.86/1.06        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.86/1.06            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.86/1.06               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.86/1.06      inference('sup-', [status(thm)], ['17', '18'])).
% 0.86/1.06  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf('21', plain,
% 0.86/1.06      (((k2_pre_topc @ sk_A @ sk_B)
% 0.86/1.06         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.86/1.06            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.86/1.06      inference('demod', [status(thm)], ['19', '20'])).
% 0.86/1.06  thf('22', plain,
% 0.86/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf(t3_subset, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.86/1.06  thf('23', plain,
% 0.86/1.06      (![X14 : $i, X15 : $i]:
% 0.86/1.06         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.86/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.86/1.06  thf('24', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.86/1.06      inference('sup-', [status(thm)], ['22', '23'])).
% 0.86/1.06  thf('25', plain,
% 0.86/1.06      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf(t44_tops_1, axiom,
% 0.86/1.06    (![A:$i]:
% 0.86/1.06     ( ( l1_pre_topc @ A ) =>
% 0.86/1.06       ( ![B:$i]:
% 0.86/1.06         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.06           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.86/1.06  thf('26', plain,
% 0.86/1.06      (![X23 : $i, X24 : $i]:
% 0.86/1.06         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.86/1.06          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ X23)
% 0.86/1.06          | ~ (l1_pre_topc @ X24))),
% 0.86/1.06      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.86/1.06  thf('27', plain,
% 0.86/1.06      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.86/1.06      inference('sup-', [status(thm)], ['25', '26'])).
% 0.86/1.06  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf('29', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.86/1.06      inference('demod', [status(thm)], ['27', '28'])).
% 0.86/1.06  thf(t12_xboole_1, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.86/1.06  thf('30', plain,
% 0.86/1.06      (![X9 : $i, X10 : $i]:
% 0.86/1.06         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.86/1.06      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.86/1.06  thf('31', plain,
% 0.86/1.06      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 0.86/1.06      inference('sup-', [status(thm)], ['29', '30'])).
% 0.86/1.06  thf(t11_xboole_1, axiom,
% 0.86/1.06    (![A:$i,B:$i,C:$i]:
% 0.86/1.06     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.86/1.06  thf('32', plain,
% 0.86/1.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.86/1.06         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.86/1.06      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.86/1.06  thf('33', plain,
% 0.86/1.06      (![X0 : $i]:
% 0.86/1.06         (~ (r1_tarski @ sk_B @ X0)
% 0.86/1.06          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['31', '32'])).
% 0.86/1.06  thf('34', plain,
% 0.86/1.06      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.86/1.06      inference('sup-', [status(thm)], ['24', '33'])).
% 0.86/1.06  thf('35', plain,
% 0.86/1.06      (![X14 : $i, X16 : $i]:
% 0.86/1.06         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.86/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.86/1.06  thf('36', plain,
% 0.86/1.06      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.86/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.06      inference('sup-', [status(thm)], ['34', '35'])).
% 0.86/1.06  thf(projectivity_k2_pre_topc, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( ( l1_pre_topc @ A ) & 
% 0.86/1.06         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.86/1.06       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.86/1.06         ( k2_pre_topc @ A @ B ) ) ))).
% 0.86/1.06  thf('37', plain,
% 0.86/1.06      (![X17 : $i, X18 : $i]:
% 0.86/1.06         (~ (l1_pre_topc @ X17)
% 0.86/1.06          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.86/1.06          | ((k2_pre_topc @ X17 @ (k2_pre_topc @ X17 @ X18))
% 0.86/1.06              = (k2_pre_topc @ X17 @ X18)))),
% 0.86/1.06      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.86/1.06  thf('38', plain,
% 0.86/1.06      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.86/1.06          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.86/1.06        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.06      inference('sup-', [status(thm)], ['36', '37'])).
% 0.86/1.06  thf('39', plain,
% 0.86/1.06      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.86/1.06      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.86/1.06  thf('40', plain,
% 0.86/1.06      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.86/1.06      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.86/1.06  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.06  thf('42', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.86/1.06      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.86/1.06  thf('43', plain,
% 0.86/1.06      (((sk_B)
% 0.86/1.06         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.86/1.06            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.86/1.06      inference('demod', [status(thm)], ['21', '42'])).
% 0.86/1.06  thf('44', plain,
% 0.86/1.06      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.86/1.06      inference('sup+', [status(thm)], ['16', '43'])).
% 0.86/1.06  thf(d10_xboole_0, axiom,
% 0.86/1.06    (![A:$i,B:$i]:
% 0.86/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.86/1.06  thf('45', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.86/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.86/1.06  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.86/1.06      inference('simplify', [status(thm)], ['45'])).
% 0.86/1.06  thf(t10_xboole_1, axiom,
% 0.86/1.06    (![A:$i,B:$i,C:$i]:
% 0.86/1.06     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.86/1.06  thf('47', plain,
% 0.86/1.06      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.86/1.06         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.86/1.06      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.86/1.06  thf('48', plain,
% 0.86/1.06      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.86/1.06      inference('sup-', [status(thm)], ['46', '47'])).
% 0.86/1.06  thf('49', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.86/1.06      inference('sup+', [status(thm)], ['44', '48'])).
% 0.86/1.06  thf('50', plain, ($false), inference('demod', [status(thm)], ['7', '49'])).
% 0.86/1.06  
% 0.86/1.06  % SZS output end Refutation
% 0.86/1.06  
% 0.86/1.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
