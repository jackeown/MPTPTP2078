%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dNTD3Pnbfe

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:44 EST 2020

% Result     : Theorem 4.20s
% Output     : Refutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 141 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  576 (1588 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X7 @ X8 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X21 @ ( k2_pre_topc @ X21 @ X20 ) ) @ ( k2_tops_1 @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('40',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['27','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['7','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dNTD3Pnbfe
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:19:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.20/4.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.20/4.39  % Solved by: fo/fo7.sh
% 4.20/4.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.20/4.39  % done 2547 iterations in 3.941s
% 4.20/4.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.20/4.39  % SZS output start Refutation
% 4.20/4.39  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.20/4.39  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 4.20/4.39  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.20/4.39  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 4.20/4.39  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 4.20/4.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.20/4.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.20/4.39  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.20/4.39  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.20/4.39  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.20/4.39  thf(sk_A_type, type, sk_A: $i).
% 4.20/4.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.20/4.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.20/4.39  thf(sk_B_type, type, sk_B: $i).
% 4.20/4.39  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 4.20/4.39  thf(t103_tops_1, conjecture,
% 4.20/4.39    (![A:$i]:
% 4.20/4.39     ( ( l1_pre_topc @ A ) =>
% 4.20/4.39       ( ![B:$i]:
% 4.20/4.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.20/4.39           ( ( v5_tops_1 @ B @ A ) =>
% 4.20/4.39             ( r1_tarski @
% 4.20/4.39               ( k2_tops_1 @ A @ B ) @ 
% 4.20/4.39               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 4.20/4.39  thf(zf_stmt_0, negated_conjecture,
% 4.20/4.39    (~( ![A:$i]:
% 4.20/4.39        ( ( l1_pre_topc @ A ) =>
% 4.20/4.39          ( ![B:$i]:
% 4.20/4.39            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.20/4.39              ( ( v5_tops_1 @ B @ A ) =>
% 4.20/4.39                ( r1_tarski @
% 4.20/4.39                  ( k2_tops_1 @ A @ B ) @ 
% 4.20/4.39                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 4.20/4.39    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 4.20/4.39  thf('0', plain,
% 4.20/4.39      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.39          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.20/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.20/4.39  thf('1', plain,
% 4.20/4.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.20/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.20/4.39  thf(d7_tops_1, axiom,
% 4.20/4.39    (![A:$i]:
% 4.20/4.39     ( ( l1_pre_topc @ A ) =>
% 4.20/4.39       ( ![B:$i]:
% 4.20/4.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.20/4.39           ( ( v5_tops_1 @ B @ A ) <=>
% 4.20/4.39             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 4.20/4.39  thf('2', plain,
% 4.20/4.39      (![X12 : $i, X13 : $i]:
% 4.20/4.39         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 4.20/4.39          | ~ (v5_tops_1 @ X12 @ X13)
% 4.20/4.39          | ((X12) = (k2_pre_topc @ X13 @ (k1_tops_1 @ X13 @ X12)))
% 4.20/4.39          | ~ (l1_pre_topc @ X13))),
% 4.20/4.39      inference('cnf', [status(esa)], [d7_tops_1])).
% 4.20/4.39  thf('3', plain,
% 4.20/4.39      ((~ (l1_pre_topc @ sk_A)
% 4.20/4.39        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.20/4.39        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 4.20/4.39      inference('sup-', [status(thm)], ['1', '2'])).
% 4.20/4.39  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 4.20/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.20/4.39  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 4.20/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.20/4.39  thf('6', plain,
% 4.20/4.39      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.20/4.39      inference('demod', [status(thm)], ['3', '4', '5'])).
% 4.20/4.39  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 4.20/4.39      inference('demod', [status(thm)], ['0', '6'])).
% 4.20/4.39  thf('8', plain,
% 4.20/4.39      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.20/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.20/4.39  thf(dt_k1_tops_1, axiom,
% 4.20/4.39    (![A:$i,B:$i]:
% 4.20/4.39     ( ( ( l1_pre_topc @ A ) & 
% 4.20/4.39         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.20/4.39       ( m1_subset_1 @
% 4.20/4.39         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.20/4.39  thf('9', plain,
% 4.20/4.39      (![X14 : $i, X15 : $i]:
% 4.20/4.39         (~ (l1_pre_topc @ X14)
% 4.20/4.39          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 4.20/4.39          | (m1_subset_1 @ (k1_tops_1 @ X14 @ X15) @ 
% 4.20/4.39             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 4.20/4.39      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 4.20/4.39  thf('10', plain,
% 4.20/4.39      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.39         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.20/4.39        | ~ (l1_pre_topc @ sk_A))),
% 4.20/4.39      inference('sup-', [status(thm)], ['8', '9'])).
% 4.20/4.39  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 4.20/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.20/4.39  thf('12', plain,
% 4.20/4.39      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.39        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.20/4.39      inference('demod', [status(thm)], ['10', '11'])).
% 4.20/4.39  thf(dt_k2_tops_1, axiom,
% 4.20/4.39    (![A:$i,B:$i]:
% 4.20/4.39     ( ( ( l1_pre_topc @ A ) & 
% 4.20/4.39         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.20/4.39       ( m1_subset_1 @
% 4.20/4.39         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.20/4.39  thf('13', plain,
% 4.20/4.39      (![X16 : $i, X17 : $i]:
% 4.20/4.39         (~ (l1_pre_topc @ X16)
% 4.20/4.39          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 4.20/4.39          | (m1_subset_1 @ (k2_tops_1 @ X16 @ X17) @ 
% 4.20/4.39             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 4.20/4.39      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 4.20/4.39  thf('14', plain,
% 4.20/4.39      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.20/4.39         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.20/4.39        | ~ (l1_pre_topc @ sk_A))),
% 4.20/4.39      inference('sup-', [status(thm)], ['12', '13'])).
% 4.20/4.39  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 4.20/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.20/4.39  thf('16', plain,
% 4.20/4.39      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 4.20/4.39        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.20/4.39      inference('demod', [status(thm)], ['14', '15'])).
% 4.20/4.39  thf('17', plain,
% 4.20/4.39      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.39        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.20/4.39      inference('demod', [status(thm)], ['10', '11'])).
% 4.20/4.39  thf(redefinition_k4_subset_1, axiom,
% 4.20/4.39    (![A:$i,B:$i,C:$i]:
% 4.20/4.39     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 4.20/4.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.20/4.39       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 4.20/4.39  thf('18', plain,
% 4.20/4.39      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.20/4.39         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 4.20/4.39          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 4.20/4.39          | ((k4_subset_1 @ X10 @ X9 @ X11) = (k2_xboole_0 @ X9 @ X11)))),
% 4.20/4.39      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 4.20/4.39  thf('19', plain,
% 4.20/4.39      (![X0 : $i]:
% 4.20/4.39         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 4.20/4.39            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 4.20/4.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.20/4.39      inference('sup-', [status(thm)], ['17', '18'])).
% 4.20/4.39  thf('20', plain,
% 4.20/4.39      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.39         (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 4.20/4.39         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.39            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.20/4.39      inference('sup-', [status(thm)], ['16', '19'])).
% 4.20/4.39  thf('21', plain,
% 4.20/4.39      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.39        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.20/4.39      inference('demod', [status(thm)], ['10', '11'])).
% 4.20/4.39  thf(t65_tops_1, axiom,
% 4.20/4.39    (![A:$i]:
% 4.20/4.39     ( ( l1_pre_topc @ A ) =>
% 4.20/4.39       ( ![B:$i]:
% 4.20/4.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.20/4.39           ( ( k2_pre_topc @ A @ B ) =
% 4.20/4.39             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.20/4.39  thf('22', plain,
% 4.20/4.39      (![X18 : $i, X19 : $i]:
% 4.20/4.39         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 4.20/4.39          | ((k2_pre_topc @ X19 @ X18)
% 4.20/4.39              = (k4_subset_1 @ (u1_struct_0 @ X19) @ X18 @ 
% 4.20/4.39                 (k2_tops_1 @ X19 @ X18)))
% 4.20/4.39          | ~ (l1_pre_topc @ X19))),
% 4.20/4.39      inference('cnf', [status(esa)], [t65_tops_1])).
% 4.20/4.39  thf('23', plain,
% 4.20/4.39      ((~ (l1_pre_topc @ sk_A)
% 4.20/4.39        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 4.20/4.39            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.20/4.39               (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.39               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 4.20/4.39      inference('sup-', [status(thm)], ['21', '22'])).
% 4.20/4.39  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 4.20/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.20/4.39  thf('25', plain,
% 4.20/4.39      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.20/4.39      inference('demod', [status(thm)], ['3', '4', '5'])).
% 4.20/4.39  thf('26', plain,
% 4.20/4.39      (((sk_B)
% 4.20/4.39         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.40            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.20/4.40      inference('demod', [status(thm)], ['23', '24', '25'])).
% 4.20/4.40  thf('27', plain,
% 4.20/4.40      (((sk_B)
% 4.20/4.40         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.40            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.20/4.40      inference('sup+', [status(thm)], ['20', '26'])).
% 4.20/4.40  thf(commutativity_k2_tarski, axiom,
% 4.20/4.40    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 4.20/4.40  thf('28', plain,
% 4.20/4.40      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 4.20/4.40      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 4.20/4.40  thf(l51_zfmisc_1, axiom,
% 4.20/4.40    (![A:$i,B:$i]:
% 4.20/4.40     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 4.20/4.40  thf('29', plain,
% 4.20/4.40      (![X7 : $i, X8 : $i]:
% 4.20/4.40         ((k3_tarski @ (k2_tarski @ X7 @ X8)) = (k2_xboole_0 @ X7 @ X8))),
% 4.20/4.40      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.20/4.40  thf('30', plain,
% 4.20/4.40      (![X0 : $i, X1 : $i]:
% 4.20/4.40         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 4.20/4.40      inference('sup+', [status(thm)], ['28', '29'])).
% 4.20/4.40  thf('31', plain,
% 4.20/4.40      (![X7 : $i, X8 : $i]:
% 4.20/4.40         ((k3_tarski @ (k2_tarski @ X7 @ X8)) = (k2_xboole_0 @ X7 @ X8))),
% 4.20/4.40      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 4.20/4.40  thf('32', plain,
% 4.20/4.40      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.20/4.40      inference('sup+', [status(thm)], ['30', '31'])).
% 4.20/4.40  thf(t7_xboole_1, axiom,
% 4.20/4.40    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.20/4.40  thf('33', plain,
% 4.20/4.40      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 4.20/4.40      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.20/4.40  thf('34', plain,
% 4.20/4.40      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.20/4.40      inference('sup+', [status(thm)], ['32', '33'])).
% 4.20/4.40  thf('35', plain,
% 4.20/4.40      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.40        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.20/4.40      inference('demod', [status(thm)], ['10', '11'])).
% 4.20/4.40  thf(t72_tops_1, axiom,
% 4.20/4.40    (![A:$i]:
% 4.20/4.40     ( ( l1_pre_topc @ A ) =>
% 4.20/4.40       ( ![B:$i]:
% 4.20/4.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.20/4.40           ( r1_tarski @
% 4.20/4.40             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 4.20/4.40             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 4.20/4.40  thf('36', plain,
% 4.20/4.40      (![X20 : $i, X21 : $i]:
% 4.20/4.40         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 4.20/4.40          | (r1_tarski @ (k2_tops_1 @ X21 @ (k2_pre_topc @ X21 @ X20)) @ 
% 4.20/4.40             (k2_tops_1 @ X21 @ X20))
% 4.20/4.40          | ~ (l1_pre_topc @ X21))),
% 4.20/4.40      inference('cnf', [status(esa)], [t72_tops_1])).
% 4.20/4.40  thf('37', plain,
% 4.20/4.40      ((~ (l1_pre_topc @ sk_A)
% 4.20/4.40        | (r1_tarski @ 
% 4.20/4.40           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 4.20/4.40           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.20/4.40      inference('sup-', [status(thm)], ['35', '36'])).
% 4.20/4.40  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 4.20/4.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.20/4.40  thf('39', plain,
% 4.20/4.40      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.20/4.40      inference('demod', [status(thm)], ['3', '4', '5'])).
% 4.20/4.40  thf('40', plain,
% 4.20/4.40      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.40        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.20/4.40      inference('demod', [status(thm)], ['37', '38', '39'])).
% 4.20/4.40  thf(t1_xboole_1, axiom,
% 4.20/4.40    (![A:$i,B:$i,C:$i]:
% 4.20/4.40     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 4.20/4.40       ( r1_tarski @ A @ C ) ))).
% 4.20/4.40  thf('41', plain,
% 4.20/4.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.20/4.40         (~ (r1_tarski @ X0 @ X1)
% 4.20/4.40          | ~ (r1_tarski @ X1 @ X2)
% 4.20/4.40          | (r1_tarski @ X0 @ X2))),
% 4.20/4.40      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.20/4.40  thf('42', plain,
% 4.20/4.40      (![X0 : $i]:
% 4.20/4.40         ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 4.20/4.40          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 4.20/4.40      inference('sup-', [status(thm)], ['40', '41'])).
% 4.20/4.40  thf('43', plain,
% 4.20/4.40      (![X0 : $i]:
% 4.20/4.40         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 4.20/4.40          (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.20/4.40      inference('sup-', [status(thm)], ['34', '42'])).
% 4.20/4.40  thf('44', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 4.20/4.40      inference('sup+', [status(thm)], ['27', '43'])).
% 4.20/4.40  thf('45', plain, ($false), inference('demod', [status(thm)], ['7', '44'])).
% 4.20/4.40  
% 4.20/4.40  % SZS output end Refutation
% 4.20/4.40  
% 4.20/4.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
