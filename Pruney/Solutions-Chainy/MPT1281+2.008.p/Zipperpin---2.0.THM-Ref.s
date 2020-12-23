%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eS9SkYbzoH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:45 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 137 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  599 (1597 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v5_tops_1 @ X10 @ X11 )
      | ( X10
        = ( k2_pre_topc @ X11 @ ( k1_tops_1 @ X11 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
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

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k4_subset_1 @ X8 @ X7 @ X9 )
        = ( k2_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ ( k2_tops_1 @ X17 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X19 @ ( k1_tops_1 @ X19 @ X18 ) ) @ ( k2_tops_1 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t71_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X21 @ ( k2_pre_topc @ X21 @ X20 ) ) @ ( k2_tops_1 @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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

thf('40',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('41',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','40'])).

thf('42',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','41'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['7','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eS9SkYbzoH
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 09:45:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.32  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.35/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.61  % Solved by: fo/fo7.sh
% 0.35/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.61  % done 184 iterations in 0.175s
% 0.35/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.61  % SZS output start Refutation
% 0.35/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.35/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.35/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.61  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.35/0.61  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.35/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.35/0.61  thf(t103_tops_1, conjecture,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( l1_pre_topc @ A ) =>
% 0.35/0.61       ( ![B:$i]:
% 0.35/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.61           ( ( v5_tops_1 @ B @ A ) =>
% 0.35/0.61             ( r1_tarski @
% 0.35/0.61               ( k2_tops_1 @ A @ B ) @ 
% 0.35/0.61               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.61    (~( ![A:$i]:
% 0.35/0.61        ( ( l1_pre_topc @ A ) =>
% 0.35/0.61          ( ![B:$i]:
% 0.35/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.61              ( ( v5_tops_1 @ B @ A ) =>
% 0.35/0.61                ( r1_tarski @
% 0.35/0.61                  ( k2_tops_1 @ A @ B ) @ 
% 0.35/0.61                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.35/0.61    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.35/0.61  thf('0', plain,
% 0.35/0.61      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('1', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(d7_tops_1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( l1_pre_topc @ A ) =>
% 0.35/0.61       ( ![B:$i]:
% 0.35/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.61           ( ( v5_tops_1 @ B @ A ) <=>
% 0.35/0.61             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.61  thf('2', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i]:
% 0.35/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.35/0.61          | ~ (v5_tops_1 @ X10 @ X11)
% 0.35/0.61          | ((X10) = (k2_pre_topc @ X11 @ (k1_tops_1 @ X11 @ X10)))
% 0.35/0.61          | ~ (l1_pre_topc @ X11))),
% 0.35/0.61      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.35/0.61  thf('3', plain,
% 0.35/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.61        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.35/0.61        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.61  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('6', plain,
% 0.35/0.61      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.35/0.61  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.35/0.61      inference('demod', [status(thm)], ['0', '6'])).
% 0.35/0.61  thf('8', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(dt_k2_tops_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( l1_pre_topc @ A ) & 
% 0.35/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.61       ( m1_subset_1 @
% 0.35/0.61         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.61  thf('9', plain,
% 0.35/0.61      (![X14 : $i, X15 : $i]:
% 0.35/0.61         (~ (l1_pre_topc @ X14)
% 0.35/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.35/0.61          | (m1_subset_1 @ (k2_tops_1 @ X14 @ X15) @ 
% 0.35/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.35/0.61      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.35/0.61  thf('10', plain,
% 0.35/0.61      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.61  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('12', plain,
% 0.35/0.61      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.35/0.61  thf('13', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(dt_k1_tops_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( l1_pre_topc @ A ) & 
% 0.35/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.35/0.61       ( m1_subset_1 @
% 0.35/0.61         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.61  thf('14', plain,
% 0.35/0.61      (![X12 : $i, X13 : $i]:
% 0.35/0.61         (~ (l1_pre_topc @ X12)
% 0.35/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.35/0.61          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 0.35/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.35/0.61      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.35/0.61  thf('15', plain,
% 0.35/0.61      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.61      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.61  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('17', plain,
% 0.35/0.61      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.35/0.61  thf(redefinition_k4_subset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.35/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.61       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.35/0.61  thf('18', plain,
% 0.35/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.35/0.61         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.35/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 0.35/0.61          | ((k4_subset_1 @ X8 @ X7 @ X9) = (k2_xboole_0 @ X7 @ X9)))),
% 0.35/0.61      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.35/0.61  thf('19', plain,
% 0.35/0.61      (![X0 : $i]:
% 0.35/0.61         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.35/0.61            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 0.35/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.61  thf('20', plain,
% 0.35/0.61      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61         (k2_tops_1 @ sk_A @ sk_B))
% 0.35/0.61         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['12', '19'])).
% 0.35/0.61  thf('21', plain,
% 0.35/0.61      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.35/0.61  thf(t65_tops_1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( l1_pre_topc @ A ) =>
% 0.35/0.61       ( ![B:$i]:
% 0.35/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.61           ( ( k2_pre_topc @ A @ B ) =
% 0.35/0.61             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.35/0.61  thf('22', plain,
% 0.35/0.61      (![X16 : $i, X17 : $i]:
% 0.35/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.35/0.61          | ((k2_pre_topc @ X17 @ X16)
% 0.35/0.61              = (k4_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 0.35/0.61                 (k2_tops_1 @ X17 @ X16)))
% 0.35/0.61          | ~ (l1_pre_topc @ X17))),
% 0.35/0.61      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.35/0.61  thf('23', plain,
% 0.35/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.61        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.35/0.61            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.35/0.61               (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.61  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('25', plain,
% 0.35/0.61      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.35/0.61  thf('26', plain,
% 0.35/0.61      (((sk_B)
% 0.35/0.61         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.35/0.61      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.35/0.61  thf('27', plain,
% 0.35/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(t71_tops_1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( l1_pre_topc @ A ) =>
% 0.35/0.61       ( ![B:$i]:
% 0.35/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.61           ( r1_tarski @
% 0.35/0.61             ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.35/0.61  thf('28', plain,
% 0.35/0.61      (![X18 : $i, X19 : $i]:
% 0.35/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.35/0.61          | (r1_tarski @ (k2_tops_1 @ X19 @ (k1_tops_1 @ X19 @ X18)) @ 
% 0.35/0.61             (k2_tops_1 @ X19 @ X18))
% 0.35/0.61          | ~ (l1_pre_topc @ X19))),
% 0.35/0.61      inference('cnf', [status(esa)], [t71_tops_1])).
% 0.35/0.61  thf('29', plain,
% 0.35/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.61        | (r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.35/0.61           (k2_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.61  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('31', plain,
% 0.35/0.61      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.35/0.61        (k2_tops_1 @ sk_A @ sk_B))),
% 0.35/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.61  thf(d10_xboole_0, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.61  thf('32', plain,
% 0.35/0.61      (![X2 : $i, X4 : $i]:
% 0.35/0.61         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.35/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.61  thf('33', plain,
% 0.35/0.61      ((~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.35/0.61        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.61            = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.61  thf('34', plain,
% 0.35/0.61      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.61      inference('demod', [status(thm)], ['15', '16'])).
% 0.35/0.61  thf(t72_tops_1, axiom,
% 0.35/0.61    (![A:$i]:
% 0.35/0.61     ( ( l1_pre_topc @ A ) =>
% 0.35/0.61       ( ![B:$i]:
% 0.35/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.61           ( r1_tarski @
% 0.35/0.61             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.35/0.61             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.35/0.61  thf('35', plain,
% 0.35/0.61      (![X20 : $i, X21 : $i]:
% 0.35/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.35/0.61          | (r1_tarski @ (k2_tops_1 @ X21 @ (k2_pre_topc @ X21 @ X20)) @ 
% 0.35/0.61             (k2_tops_1 @ X21 @ X20))
% 0.35/0.61          | ~ (l1_pre_topc @ X21))),
% 0.35/0.61      inference('cnf', [status(esa)], [t72_tops_1])).
% 0.35/0.61  thf('36', plain,
% 0.35/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.61        | (r1_tarski @ 
% 0.35/0.61           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.35/0.61           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.61  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('38', plain,
% 0.35/0.61      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.35/0.61  thf('39', plain,
% 0.35/0.61      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.35/0.61  thf('40', plain,
% 0.35/0.61      (((k2_tops_1 @ sk_A @ sk_B)
% 0.35/0.61         = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('demod', [status(thm)], ['33', '39'])).
% 0.35/0.61  thf('41', plain,
% 0.35/0.61      (((sk_B)
% 0.35/0.61         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.35/0.61            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('demod', [status(thm)], ['26', '40'])).
% 0.35/0.61  thf('42', plain,
% 0.35/0.61      (((sk_B)
% 0.35/0.61         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.35/0.61      inference('sup+', [status(thm)], ['20', '41'])).
% 0.35/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.35/0.61  thf('43', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.35/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.35/0.61  thf(t7_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.35/0.61  thf('44', plain,
% 0.35/0.61      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.35/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.35/0.61  thf('45', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.35/0.61      inference('sup+', [status(thm)], ['43', '44'])).
% 0.35/0.61  thf('46', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.35/0.61      inference('sup+', [status(thm)], ['42', '45'])).
% 0.35/0.61  thf('47', plain, ($false), inference('demod', [status(thm)], ['7', '46'])).
% 0.35/0.61  
% 0.35/0.61  % SZS output end Refutation
% 0.35/0.61  
% 0.35/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
