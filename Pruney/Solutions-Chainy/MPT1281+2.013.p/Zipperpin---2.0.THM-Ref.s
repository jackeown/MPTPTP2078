%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UIRBDSIFPF

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:46 EST 2020

% Result     : Theorem 5.51s
% Output     : Refutation 5.51s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 136 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  561 (1565 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v5_tops_1 @ X12 @ X13 )
      | ( X12
        = ( k2_pre_topc @ X13 @ ( k1_tops_1 @ X13 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k4_subset_1 @ X10 @ X9 @ X11 )
        = ( k2_xboole_0 @ X9 @ X11 ) ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ ( k2_tops_1 @ X19 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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

thf('28',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X21 @ ( k2_pre_topc @ X21 @ X20 ) ) @ ( k2_tops_1 @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('33',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['27','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['7','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UIRBDSIFPF
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:01:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 5.51/5.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.51/5.77  % Solved by: fo/fo7.sh
% 5.51/5.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.51/5.77  % done 6028 iterations in 5.327s
% 5.51/5.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.51/5.77  % SZS output start Refutation
% 5.51/5.77  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 5.51/5.77  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 5.51/5.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.51/5.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.51/5.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.51/5.77  thf(sk_B_type, type, sk_B: $i).
% 5.51/5.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.51/5.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.51/5.77  thf(sk_A_type, type, sk_A: $i).
% 5.51/5.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.51/5.77  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 5.51/5.77  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.51/5.77  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 5.51/5.77  thf(t103_tops_1, conjecture,
% 5.51/5.77    (![A:$i]:
% 5.51/5.77     ( ( l1_pre_topc @ A ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.51/5.78           ( ( v5_tops_1 @ B @ A ) =>
% 5.51/5.78             ( r1_tarski @
% 5.51/5.78               ( k2_tops_1 @ A @ B ) @ 
% 5.51/5.78               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 5.51/5.78  thf(zf_stmt_0, negated_conjecture,
% 5.51/5.78    (~( ![A:$i]:
% 5.51/5.78        ( ( l1_pre_topc @ A ) =>
% 5.51/5.78          ( ![B:$i]:
% 5.51/5.78            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.51/5.78              ( ( v5_tops_1 @ B @ A ) =>
% 5.51/5.78                ( r1_tarski @
% 5.51/5.78                  ( k2_tops_1 @ A @ B ) @ 
% 5.51/5.78                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 5.51/5.78    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 5.51/5.78  thf('0', plain,
% 5.51/5.78      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('1', plain,
% 5.51/5.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf(d7_tops_1, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( l1_pre_topc @ A ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.51/5.78           ( ( v5_tops_1 @ B @ A ) <=>
% 5.51/5.78             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 5.51/5.78  thf('2', plain,
% 5.51/5.78      (![X12 : $i, X13 : $i]:
% 5.51/5.78         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 5.51/5.78          | ~ (v5_tops_1 @ X12 @ X13)
% 5.51/5.78          | ((X12) = (k2_pre_topc @ X13 @ (k1_tops_1 @ X13 @ X12)))
% 5.51/5.78          | ~ (l1_pre_topc @ X13))),
% 5.51/5.78      inference('cnf', [status(esa)], [d7_tops_1])).
% 5.51/5.78  thf('3', plain,
% 5.51/5.78      ((~ (l1_pre_topc @ sk_A)
% 5.51/5.78        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 5.51/5.78        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['1', '2'])).
% 5.51/5.78  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('6', plain,
% 5.51/5.78      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.51/5.78      inference('demod', [status(thm)], ['3', '4', '5'])).
% 5.51/5.78  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.51/5.78      inference('demod', [status(thm)], ['0', '6'])).
% 5.51/5.78  thf('8', plain,
% 5.51/5.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf(dt_k1_tops_1, axiom,
% 5.51/5.78    (![A:$i,B:$i]:
% 5.51/5.78     ( ( ( l1_pre_topc @ A ) & 
% 5.51/5.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.51/5.78       ( m1_subset_1 @
% 5.51/5.78         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.51/5.78  thf('9', plain,
% 5.51/5.78      (![X14 : $i, X15 : $i]:
% 5.51/5.78         (~ (l1_pre_topc @ X14)
% 5.51/5.78          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.51/5.78          | (m1_subset_1 @ (k1_tops_1 @ X14 @ X15) @ 
% 5.51/5.78             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 5.51/5.78      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 5.51/5.78  thf('10', plain,
% 5.51/5.78      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.51/5.78        | ~ (l1_pre_topc @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['8', '9'])).
% 5.51/5.78  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('12', plain,
% 5.51/5.78      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('demod', [status(thm)], ['10', '11'])).
% 5.51/5.78  thf(dt_k2_tops_1, axiom,
% 5.51/5.78    (![A:$i,B:$i]:
% 5.51/5.78     ( ( ( l1_pre_topc @ A ) & 
% 5.51/5.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.51/5.78       ( m1_subset_1 @
% 5.51/5.78         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.51/5.78  thf('13', plain,
% 5.51/5.78      (![X16 : $i, X17 : $i]:
% 5.51/5.78         (~ (l1_pre_topc @ X16)
% 5.51/5.78          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 5.51/5.78          | (m1_subset_1 @ (k2_tops_1 @ X16 @ X17) @ 
% 5.51/5.78             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 5.51/5.78      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 5.51/5.78  thf('14', plain,
% 5.51/5.78      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 5.51/5.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.51/5.78        | ~ (l1_pre_topc @ sk_A))),
% 5.51/5.78      inference('sup-', [status(thm)], ['12', '13'])).
% 5.51/5.78  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('16', plain,
% 5.51/5.78      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 5.51/5.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('demod', [status(thm)], ['14', '15'])).
% 5.51/5.78  thf('17', plain,
% 5.51/5.78      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('demod', [status(thm)], ['10', '11'])).
% 5.51/5.78  thf(redefinition_k4_subset_1, axiom,
% 5.51/5.78    (![A:$i,B:$i,C:$i]:
% 5.51/5.78     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.51/5.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.51/5.78       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 5.51/5.78  thf('18', plain,
% 5.51/5.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.51/5.78         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 5.51/5.78          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 5.51/5.78          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 5.51/5.78      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.51/5.78  thf('19', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 5.51/5.78            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 5.51/5.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['17', '18'])).
% 5.51/5.78  thf('20', plain,
% 5.51/5.78      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78         (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 5.51/5.78         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['16', '19'])).
% 5.51/5.78  thf('21', plain,
% 5.51/5.78      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('demod', [status(thm)], ['10', '11'])).
% 5.51/5.78  thf(t65_tops_1, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( l1_pre_topc @ A ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.51/5.78           ( ( k2_pre_topc @ A @ B ) =
% 5.51/5.78             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.51/5.78  thf('22', plain,
% 5.51/5.78      (![X18 : $i, X19 : $i]:
% 5.51/5.78         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 5.51/5.78          | ((k2_pre_topc @ X19 @ X18)
% 5.51/5.78              = (k4_subset_1 @ (u1_struct_0 @ X19) @ X18 @ 
% 5.51/5.78                 (k2_tops_1 @ X19 @ X18)))
% 5.51/5.78          | ~ (l1_pre_topc @ X19))),
% 5.51/5.78      inference('cnf', [status(esa)], [t65_tops_1])).
% 5.51/5.78  thf('23', plain,
% 5.51/5.78      ((~ (l1_pre_topc @ sk_A)
% 5.51/5.78        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 5.51/5.78            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.51/5.78               (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['21', '22'])).
% 5.51/5.78  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('25', plain,
% 5.51/5.78      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.51/5.78      inference('demod', [status(thm)], ['3', '4', '5'])).
% 5.51/5.78  thf('26', plain,
% 5.51/5.78      (((sk_B)
% 5.51/5.78         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.51/5.78      inference('demod', [status(thm)], ['23', '24', '25'])).
% 5.51/5.78  thf('27', plain,
% 5.51/5.78      (((sk_B)
% 5.51/5.78         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.51/5.78      inference('sup+', [status(thm)], ['20', '26'])).
% 5.51/5.78  thf('28', plain,
% 5.51/5.78      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.51/5.78      inference('demod', [status(thm)], ['10', '11'])).
% 5.51/5.78  thf(t72_tops_1, axiom,
% 5.51/5.78    (![A:$i]:
% 5.51/5.78     ( ( l1_pre_topc @ A ) =>
% 5.51/5.78       ( ![B:$i]:
% 5.51/5.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.51/5.78           ( r1_tarski @
% 5.51/5.78             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 5.51/5.78             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 5.51/5.78  thf('29', plain,
% 5.51/5.78      (![X20 : $i, X21 : $i]:
% 5.51/5.78         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 5.51/5.78          | (r1_tarski @ (k2_tops_1 @ X21 @ (k2_pre_topc @ X21 @ X20)) @ 
% 5.51/5.78             (k2_tops_1 @ X21 @ X20))
% 5.51/5.78          | ~ (l1_pre_topc @ X21))),
% 5.51/5.78      inference('cnf', [status(esa)], [t72_tops_1])).
% 5.51/5.78  thf('30', plain,
% 5.51/5.78      ((~ (l1_pre_topc @ sk_A)
% 5.51/5.78        | (r1_tarski @ 
% 5.51/5.78           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 5.51/5.78           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.51/5.78      inference('sup-', [status(thm)], ['28', '29'])).
% 5.51/5.78  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 5.51/5.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.51/5.78  thf('32', plain,
% 5.51/5.78      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.51/5.78      inference('demod', [status(thm)], ['3', '4', '5'])).
% 5.51/5.78  thf('33', plain,
% 5.51/5.78      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.51/5.78      inference('demod', [status(thm)], ['30', '31', '32'])).
% 5.51/5.78  thf(t12_xboole_1, axiom,
% 5.51/5.78    (![A:$i,B:$i]:
% 5.51/5.78     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 5.51/5.78  thf('34', plain,
% 5.51/5.78      (![X5 : $i, X6 : $i]:
% 5.51/5.78         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 5.51/5.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 5.51/5.78  thf('35', plain,
% 5.51/5.78      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78         (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 5.51/5.78         = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.51/5.78      inference('sup-', [status(thm)], ['33', '34'])).
% 5.51/5.78  thf(commutativity_k2_xboole_0, axiom,
% 5.51/5.78    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 5.51/5.78  thf('36', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.51/5.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.51/5.78  thf(t7_xboole_1, axiom,
% 5.51/5.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.51/5.78  thf('37', plain,
% 5.51/5.78      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 5.51/5.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.51/5.78  thf('38', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.51/5.78      inference('sup+', [status(thm)], ['36', '37'])).
% 5.51/5.78  thf(t11_xboole_1, axiom,
% 5.51/5.78    (![A:$i,B:$i,C:$i]:
% 5.51/5.78     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 5.51/5.78  thf('39', plain,
% 5.51/5.78      (![X2 : $i, X3 : $i, X4 : $i]:
% 5.51/5.78         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 5.51/5.78      inference('cnf', [status(esa)], [t11_xboole_1])).
% 5.51/5.78  thf('40', plain,
% 5.51/5.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.51/5.78         (r1_tarski @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 5.51/5.78      inference('sup-', [status(thm)], ['38', '39'])).
% 5.51/5.78  thf('41', plain,
% 5.51/5.78      (![X0 : $i]:
% 5.51/5.78         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.51/5.78          (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.51/5.78      inference('sup+', [status(thm)], ['35', '40'])).
% 5.51/5.78  thf('42', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.51/5.78      inference('sup+', [status(thm)], ['27', '41'])).
% 5.51/5.78  thf('43', plain, ($false), inference('demod', [status(thm)], ['7', '42'])).
% 5.51/5.78  
% 5.51/5.78  % SZS output end Refutation
% 5.51/5.78  
% 5.63/5.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
