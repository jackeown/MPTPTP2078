%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CGJn19xQ6d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:47 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 159 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  619 (1925 expanded)
%              Number of equality atoms :   30 (  40 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v5_tops_1 @ X39 @ X40 )
      | ( X39
        = ( k2_pre_topc @ X40 @ ( k1_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( l1_pre_topc @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X43 @ X44 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k4_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_subset_1 @ X32 @ X33 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k2_pre_topc @ X46 @ X45 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X46 ) @ X45 @ ( k2_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( ( k2_pre_topc @ X37 @ ( k2_pre_topc @ X37 @ X38 ) )
        = ( k2_pre_topc @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('42',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('43',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('45',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','43','44'])).

thf('46',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['27','45'])).

thf('47',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['16','46'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('49',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['7','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CGJn19xQ6d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:27:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 262 iterations in 0.285s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.55/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.74  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.55/0.74  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.55/0.74  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.55/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.55/0.74  thf(t103_tops_1, conjecture,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74           ( ( v5_tops_1 @ B @ A ) =>
% 0.55/0.74             ( r1_tarski @
% 0.55/0.74               ( k2_tops_1 @ A @ B ) @ 
% 0.55/0.74               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i]:
% 0.55/0.74        ( ( l1_pre_topc @ A ) =>
% 0.55/0.74          ( ![B:$i]:
% 0.55/0.74            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74              ( ( v5_tops_1 @ B @ A ) =>
% 0.55/0.74                ( r1_tarski @
% 0.55/0.74                  ( k2_tops_1 @ A @ B ) @ 
% 0.55/0.74                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.55/0.74          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(d7_tops_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74           ( ( v5_tops_1 @ B @ A ) <=>
% 0.55/0.74             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X39 : $i, X40 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.55/0.74          | ~ (v5_tops_1 @ X39 @ X40)
% 0.55/0.74          | ((X39) = (k2_pre_topc @ X40 @ (k1_tops_1 @ X40 @ X39)))
% 0.55/0.74          | ~ (l1_pre_topc @ X40))),
% 0.55/0.74      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.55/0.74        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.74  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.55/0.74  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.55/0.74      inference('demod', [status(thm)], ['0', '6'])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('9', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(dt_k2_tops_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( l1_pre_topc @ A ) & 
% 0.55/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.74       ( m1_subset_1 @
% 0.55/0.74         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      (![X43 : $i, X44 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X43)
% 0.55/0.74          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.55/0.74          | (m1_subset_1 @ (k2_tops_1 @ X43 @ X44) @ 
% 0.55/0.74             (k1_zfmisc_1 @ (u1_struct_0 @ X43))))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.55/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.55/0.74  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf(redefinition_k4_subset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.55/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.74       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.55/0.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 0.55/0.74          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.55/0.74            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.55/0.74  thf('16', plain,
% 0.55/0.74      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.55/0.74         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['8', '15'])).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(commutativity_k4_subset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.55/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.55/0.74       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.55/0.74          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 0.55/0.74          | ((k4_subset_1 @ X32 @ X31 @ X33) = (k4_subset_1 @ X32 @ X33 @ X31)))),
% 0.55/0.74      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.55/0.74            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['18', '19'])).
% 0.55/0.74  thf('21', plain,
% 0.55/0.74      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.55/0.74         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.55/0.74            sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['17', '20'])).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.55/0.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 0.55/0.74          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 0.55/0.74      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.55/0.74            = (k2_xboole_0 @ sk_B @ X0))
% 0.55/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.55/0.74  thf('26', plain,
% 0.55/0.74      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.55/0.74         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['22', '25'])).
% 0.55/0.74  thf('27', plain,
% 0.55/0.74      (((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.55/0.74         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.55/0.74            sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['21', '26'])).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t65_tops_1, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74           ( ( k2_pre_topc @ A @ B ) =
% 0.55/0.74             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      (![X45 : $i, X46 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.55/0.74          | ((k2_pre_topc @ X46 @ X45)
% 0.55/0.74              = (k4_subset_1 @ (u1_struct_0 @ X46) @ X45 @ 
% 0.55/0.74                 (k2_tops_1 @ X46 @ X45)))
% 0.55/0.74          | ~ (l1_pre_topc @ X46))),
% 0.55/0.74      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      ((~ (l1_pre_topc @ sk_A)
% 0.55/0.74        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.55/0.74            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.55/0.74               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['28', '29'])).
% 0.55/0.74  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(dt_k1_tops_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( l1_pre_topc @ A ) & 
% 0.55/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.74       ( m1_subset_1 @
% 0.55/0.74         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      (![X41 : $i, X42 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X41)
% 0.55/0.74          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.55/0.74          | (m1_subset_1 @ (k1_tops_1 @ X41 @ X42) @ 
% 0.55/0.74             (k1_zfmisc_1 @ (u1_struct_0 @ X41))))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.55/0.74         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.74  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.55/0.74        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.74      inference('demod', [status(thm)], ['34', '35'])).
% 0.55/0.74  thf(projectivity_k2_pre_topc, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( l1_pre_topc @ A ) & 
% 0.55/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.74       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.55/0.74         ( k2_pre_topc @ A @ B ) ) ))).
% 0.55/0.74  thf('37', plain,
% 0.55/0.74      (![X37 : $i, X38 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X37)
% 0.55/0.74          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.55/0.74          | ((k2_pre_topc @ X37 @ (k2_pre_topc @ X37 @ X38))
% 0.55/0.74              = (k2_pre_topc @ X37 @ X38)))),
% 0.55/0.74      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.55/0.74  thf('38', plain,
% 0.55/0.74      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.55/0.74          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.55/0.74        | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.55/0.74  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.55/0.74         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['38', '39'])).
% 0.55/0.74  thf('41', plain,
% 0.55/0.74      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.55/0.74  thf('42', plain,
% 0.55/0.74      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.55/0.74  thf('43', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.55/0.74         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['22', '25'])).
% 0.55/0.74  thf('45', plain,
% 0.55/0.74      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.55/0.74      inference('demod', [status(thm)], ['30', '31', '43', '44'])).
% 0.55/0.74  thf('46', plain,
% 0.55/0.74      (((sk_B)
% 0.55/0.74         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.55/0.74            sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['27', '45'])).
% 0.55/0.74  thf('47', plain,
% 0.55/0.74      (((sk_B) = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['16', '46'])).
% 0.55/0.74  thf(t7_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.55/0.74  thf('48', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.55/0.74  thf('49', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.55/0.74      inference('sup+', [status(thm)], ['47', '48'])).
% 0.55/0.74  thf('50', plain, ($false), inference('demod', [status(thm)], ['7', '49'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
