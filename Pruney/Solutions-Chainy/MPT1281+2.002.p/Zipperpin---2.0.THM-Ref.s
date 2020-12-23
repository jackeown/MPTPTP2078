%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fUgcIXDM85

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:44 EST 2020

% Result     : Theorem 1.97s
% Output     : Refutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 144 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  600 (1612 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X23 @ ( k2_pre_topc @ X23 @ X22 ) ) @ ( k2_tops_1 @ X23 @ X22 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['35','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['27','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['7','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fUgcIXDM85
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.97/2.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.97/2.19  % Solved by: fo/fo7.sh
% 1.97/2.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.97/2.19  % done 3254 iterations in 1.735s
% 1.97/2.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.97/2.19  % SZS output start Refutation
% 1.97/2.19  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.97/2.19  thf(sk_B_type, type, sk_B: $i).
% 1.97/2.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.97/2.19  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.97/2.19  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.97/2.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.97/2.19  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.97/2.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.97/2.19  thf(sk_A_type, type, sk_A: $i).
% 1.97/2.19  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 1.97/2.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.97/2.19  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.97/2.19  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.97/2.19  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.97/2.19  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.97/2.19  thf(t103_tops_1, conjecture,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( l1_pre_topc @ A ) =>
% 1.97/2.19       ( ![B:$i]:
% 1.97/2.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.19           ( ( v5_tops_1 @ B @ A ) =>
% 1.97/2.19             ( r1_tarski @
% 1.97/2.19               ( k2_tops_1 @ A @ B ) @ 
% 1.97/2.19               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.97/2.19  thf(zf_stmt_0, negated_conjecture,
% 1.97/2.19    (~( ![A:$i]:
% 1.97/2.19        ( ( l1_pre_topc @ A ) =>
% 1.97/2.19          ( ![B:$i]:
% 1.97/2.19            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.19              ( ( v5_tops_1 @ B @ A ) =>
% 1.97/2.19                ( r1_tarski @
% 1.97/2.19                  ( k2_tops_1 @ A @ B ) @ 
% 1.97/2.19                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.97/2.19    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 1.97/2.19  thf('0', plain,
% 1.97/2.19      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('1', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(d7_tops_1, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( l1_pre_topc @ A ) =>
% 1.97/2.19       ( ![B:$i]:
% 1.97/2.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.19           ( ( v5_tops_1 @ B @ A ) <=>
% 1.97/2.19             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.97/2.19  thf('2', plain,
% 1.97/2.19      (![X14 : $i, X15 : $i]:
% 1.97/2.19         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.97/2.19          | ~ (v5_tops_1 @ X14 @ X15)
% 1.97/2.19          | ((X14) = (k2_pre_topc @ X15 @ (k1_tops_1 @ X15 @ X14)))
% 1.97/2.19          | ~ (l1_pre_topc @ X15))),
% 1.97/2.19      inference('cnf', [status(esa)], [d7_tops_1])).
% 1.97/2.19  thf('3', plain,
% 1.97/2.19      ((~ (l1_pre_topc @ sk_A)
% 1.97/2.19        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.97/2.19        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['1', '2'])).
% 1.97/2.19  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('6', plain,
% 1.97/2.19      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.97/2.19  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.97/2.19      inference('demod', [status(thm)], ['0', '6'])).
% 1.97/2.19  thf('8', plain,
% 1.97/2.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf(dt_k1_tops_1, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ( ( l1_pre_topc @ A ) & 
% 1.97/2.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.97/2.19       ( m1_subset_1 @
% 1.97/2.19         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.97/2.19  thf('9', plain,
% 1.97/2.19      (![X16 : $i, X17 : $i]:
% 1.97/2.19         (~ (l1_pre_topc @ X16)
% 1.97/2.19          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.97/2.19          | (m1_subset_1 @ (k1_tops_1 @ X16 @ X17) @ 
% 1.97/2.19             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 1.97/2.19      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.97/2.19  thf('10', plain,
% 1.97/2.19      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.97/2.19        | ~ (l1_pre_topc @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['8', '9'])).
% 1.97/2.19  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('12', plain,
% 1.97/2.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.19      inference('demod', [status(thm)], ['10', '11'])).
% 1.97/2.19  thf(dt_k2_tops_1, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ( ( l1_pre_topc @ A ) & 
% 1.97/2.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.97/2.19       ( m1_subset_1 @
% 1.97/2.19         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.97/2.19  thf('13', plain,
% 1.97/2.19      (![X18 : $i, X19 : $i]:
% 1.97/2.19         (~ (l1_pre_topc @ X18)
% 1.97/2.19          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.97/2.19          | (m1_subset_1 @ (k2_tops_1 @ X18 @ X19) @ 
% 1.97/2.19             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 1.97/2.19      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.97/2.19  thf('14', plain,
% 1.97/2.19      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.97/2.19         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.97/2.19        | ~ (l1_pre_topc @ sk_A))),
% 1.97/2.19      inference('sup-', [status(thm)], ['12', '13'])).
% 1.97/2.19  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('16', plain,
% 1.97/2.19      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 1.97/2.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.19      inference('demod', [status(thm)], ['14', '15'])).
% 1.97/2.19  thf('17', plain,
% 1.97/2.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.19      inference('demod', [status(thm)], ['10', '11'])).
% 1.97/2.19  thf(redefinition_k4_subset_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.97/2.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.97/2.19       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.97/2.19  thf('18', plain,
% 1.97/2.19      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.97/2.19         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.97/2.19          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 1.97/2.19          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 1.97/2.19      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.97/2.19  thf('19', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.97/2.19            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 1.97/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['17', '18'])).
% 1.97/2.19  thf('20', plain,
% 1.97/2.19      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19         (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.97/2.19         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['16', '19'])).
% 1.97/2.19  thf('21', plain,
% 1.97/2.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.19      inference('demod', [status(thm)], ['10', '11'])).
% 1.97/2.19  thf(t65_tops_1, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( l1_pre_topc @ A ) =>
% 1.97/2.19       ( ![B:$i]:
% 1.97/2.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.19           ( ( k2_pre_topc @ A @ B ) =
% 1.97/2.19             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.97/2.19  thf('22', plain,
% 1.97/2.19      (![X20 : $i, X21 : $i]:
% 1.97/2.19         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.97/2.19          | ((k2_pre_topc @ X21 @ X20)
% 1.97/2.19              = (k4_subset_1 @ (u1_struct_0 @ X21) @ X20 @ 
% 1.97/2.19                 (k2_tops_1 @ X21 @ X20)))
% 1.97/2.19          | ~ (l1_pre_topc @ X21))),
% 1.97/2.19      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.97/2.19  thf('23', plain,
% 1.97/2.19      ((~ (l1_pre_topc @ sk_A)
% 1.97/2.19        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 1.97/2.19            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.97/2.19               (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['21', '22'])).
% 1.97/2.19  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('25', plain,
% 1.97/2.19      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.97/2.19  thf('26', plain,
% 1.97/2.19      (((sk_B)
% 1.97/2.19         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.97/2.19      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.97/2.19  thf('27', plain,
% 1.97/2.19      (((sk_B)
% 1.97/2.19         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.97/2.19      inference('sup+', [status(thm)], ['20', '26'])).
% 1.97/2.19  thf('28', plain,
% 1.97/2.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.97/2.19      inference('demod', [status(thm)], ['10', '11'])).
% 1.97/2.19  thf(t72_tops_1, axiom,
% 1.97/2.19    (![A:$i]:
% 1.97/2.19     ( ( l1_pre_topc @ A ) =>
% 1.97/2.19       ( ![B:$i]:
% 1.97/2.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.97/2.19           ( r1_tarski @
% 1.97/2.19             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 1.97/2.19             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 1.97/2.19  thf('29', plain,
% 1.97/2.19      (![X22 : $i, X23 : $i]:
% 1.97/2.19         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.97/2.19          | (r1_tarski @ (k2_tops_1 @ X23 @ (k2_pre_topc @ X23 @ X22)) @ 
% 1.97/2.19             (k2_tops_1 @ X23 @ X22))
% 1.97/2.19          | ~ (l1_pre_topc @ X23))),
% 1.97/2.19      inference('cnf', [status(esa)], [t72_tops_1])).
% 1.97/2.19  thf('30', plain,
% 1.97/2.19      ((~ (l1_pre_topc @ sk_A)
% 1.97/2.19        | (r1_tarski @ 
% 1.97/2.19           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 1.97/2.19           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.97/2.19      inference('sup-', [status(thm)], ['28', '29'])).
% 1.97/2.19  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.97/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.97/2.19  thf('32', plain,
% 1.97/2.19      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.97/2.19  thf('33', plain,
% 1.97/2.19      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.97/2.19  thf(t12_xboole_1, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.97/2.19  thf('34', plain,
% 1.97/2.19      (![X3 : $i, X4 : $i]:
% 1.97/2.19         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 1.97/2.19      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.97/2.19  thf('35', plain,
% 1.97/2.19      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19         (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.97/2.19         = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['33', '34'])).
% 1.97/2.19  thf(commutativity_k2_tarski, axiom,
% 1.97/2.19    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.97/2.19  thf('36', plain,
% 1.97/2.19      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 1.97/2.19      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.97/2.19  thf(l51_zfmisc_1, axiom,
% 1.97/2.19    (![A:$i,B:$i]:
% 1.97/2.19     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.97/2.19  thf('37', plain,
% 1.97/2.19      (![X9 : $i, X10 : $i]:
% 1.97/2.19         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 1.97/2.19      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.97/2.19  thf('38', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]:
% 1.97/2.19         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.97/2.19      inference('sup+', [status(thm)], ['36', '37'])).
% 1.97/2.19  thf('39', plain,
% 1.97/2.19      (![X9 : $i, X10 : $i]:
% 1.97/2.19         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 1.97/2.19      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.97/2.19  thf('40', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.97/2.19      inference('sup+', [status(thm)], ['38', '39'])).
% 1.97/2.19  thf(t7_xboole_1, axiom,
% 1.97/2.19    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.97/2.19  thf('41', plain,
% 1.97/2.19      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 1.97/2.19      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.97/2.19  thf('42', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.97/2.19      inference('sup+', [status(thm)], ['40', '41'])).
% 1.97/2.19  thf(t11_xboole_1, axiom,
% 1.97/2.19    (![A:$i,B:$i,C:$i]:
% 1.97/2.19     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 1.97/2.19  thf('43', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.19         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 1.97/2.19      inference('cnf', [status(esa)], [t11_xboole_1])).
% 1.97/2.19  thf('44', plain,
% 1.97/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.97/2.19         (r1_tarski @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.97/2.19      inference('sup-', [status(thm)], ['42', '43'])).
% 1.97/2.19  thf('45', plain,
% 1.97/2.19      (![X0 : $i]:
% 1.97/2.19         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.97/2.19          (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.97/2.19      inference('sup+', [status(thm)], ['35', '44'])).
% 1.97/2.19  thf('46', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.97/2.19      inference('sup+', [status(thm)], ['27', '45'])).
% 1.97/2.19  thf('47', plain, ($false), inference('demod', [status(thm)], ['7', '46'])).
% 1.97/2.19  
% 1.97/2.19  % SZS output end Refutation
% 1.97/2.19  
% 1.97/2.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
