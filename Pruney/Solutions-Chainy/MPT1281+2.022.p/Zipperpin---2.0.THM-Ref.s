%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zZSv40hs67

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:47 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 127 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  566 (1514 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v5_tops_1 @ X37 @ X38 )
      | ( X37
        = ( k2_pre_topc @ X38 @ ( k1_tops_1 @ X38 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
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
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X41 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) ) ),
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
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) ) ),
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

thf(commutativity_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k4_subset_1 @ A @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k4_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_subset_1 @ X32 @ X33 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k4_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('22',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('28',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( ( k2_pre_topc @ X46 @ X45 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X46 ) @ X45 @ ( k2_tops_1 @ X46 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
              = ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('33',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k2_tops_1 @ X44 @ ( k1_tops_1 @ X44 @ X43 ) )
        = ( k2_tops_1 @ X44 @ X43 ) )
      | ~ ( v5_tops_1 @ X43 @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t102_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','37'])).

thf('39',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','38'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['7','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zZSv40hs67
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 415 iterations in 0.621s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.90/1.08  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.90/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.08  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.90/1.08  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.90/1.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.08  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.90/1.08  thf(t103_tops_1, conjecture,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( l1_pre_topc @ A ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.08           ( ( v5_tops_1 @ B @ A ) =>
% 0.90/1.08             ( r1_tarski @
% 0.90/1.08               ( k2_tops_1 @ A @ B ) @ 
% 0.90/1.08               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i]:
% 0.90/1.08        ( ( l1_pre_topc @ A ) =>
% 0.90/1.08          ( ![B:$i]:
% 0.90/1.08            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.08              ( ( v5_tops_1 @ B @ A ) =>
% 0.90/1.08                ( r1_tarski @
% 0.90/1.08                  ( k2_tops_1 @ A @ B ) @ 
% 0.90/1.08                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.90/1.08  thf('0', plain,
% 0.90/1.08      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('1', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(d7_tops_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( l1_pre_topc @ A ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.08           ( ( v5_tops_1 @ B @ A ) <=>
% 0.90/1.08             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      (![X37 : $i, X38 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.90/1.08          | ~ (v5_tops_1 @ X37 @ X38)
% 0.90/1.08          | ((X37) = (k2_pre_topc @ X38 @ (k1_tops_1 @ X38 @ X37)))
% 0.90/1.08          | ~ (l1_pre_topc @ X38))),
% 0.90/1.08      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.90/1.08  thf('3', plain,
% 0.90/1.08      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.08        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.90/1.08        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.08  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.90/1.08  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.90/1.08      inference('demod', [status(thm)], ['0', '6'])).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(dt_k2_tops_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( l1_pre_topc @ A ) & 
% 0.90/1.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.08       ( m1_subset_1 @
% 0.90/1.08         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X41 : $i, X42 : $i]:
% 0.90/1.08         (~ (l1_pre_topc @ X41)
% 0.90/1.08          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 0.90/1.08          | (m1_subset_1 @ (k2_tops_1 @ X41 @ X42) @ 
% 0.90/1.08             (k1_zfmisc_1 @ (u1_struct_0 @ X41))))),
% 0.90/1.08      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.08        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['8', '9'])).
% 0.90/1.08  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('12', plain,
% 0.90/1.08      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.08      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.08  thf('13', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(dt_k1_tops_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( l1_pre_topc @ A ) & 
% 0.90/1.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.90/1.08       ( m1_subset_1 @
% 0.90/1.08         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.90/1.08  thf('14', plain,
% 0.90/1.08      (![X39 : $i, X40 : $i]:
% 0.90/1.08         (~ (l1_pre_topc @ X39)
% 0.90/1.08          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.90/1.08          | (m1_subset_1 @ (k1_tops_1 @ X39 @ X40) @ 
% 0.90/1.08             (k1_zfmisc_1 @ (u1_struct_0 @ X39))))),
% 0.90/1.08      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.08        | ~ (l1_pre_topc @ sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['13', '14'])).
% 0.90/1.08  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('17', plain,
% 0.90/1.08      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.08      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.08  thf(commutativity_k4_subset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.90/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.90/1.08       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 0.90/1.08  thf('18', plain,
% 0.90/1.08      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 0.90/1.08          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32))
% 0.90/1.08          | ((k4_subset_1 @ X32 @ X31 @ X33) = (k4_subset_1 @ X32 @ X33 @ X31)))),
% 0.90/1.08      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 0.90/1.08  thf('19', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.90/1.08            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.90/1.08               (k1_tops_1 @ sk_A @ sk_B)))
% 0.90/1.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['17', '18'])).
% 0.90/1.08  thf('20', plain,
% 0.90/1.08      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08         (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.08         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['12', '19'])).
% 0.90/1.08  thf('21', plain,
% 0.90/1.08      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.08      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.08      inference('demod', [status(thm)], ['10', '11'])).
% 0.90/1.08  thf(redefinition_k4_subset_1, axiom,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.90/1.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.90/1.08       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.90/1.08  thf('23', plain,
% 0.90/1.08      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.90/1.08          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 0.90/1.08          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 0.90/1.08      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.90/1.08  thf('24', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 0.90/1.08            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 0.90/1.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.08  thf('25', plain,
% 0.90/1.08      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08         (k1_tops_1 @ sk_A @ sk_B))
% 0.90/1.08         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['21', '24'])).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08         (k2_tops_1 @ sk_A @ sk_B))
% 0.90/1.08         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('demod', [status(thm)], ['20', '25'])).
% 0.90/1.08  thf('27', plain,
% 0.90/1.08      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.08      inference('demod', [status(thm)], ['15', '16'])).
% 0.90/1.08  thf(t65_tops_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( l1_pre_topc @ A ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.08           ( ( k2_pre_topc @ A @ B ) =
% 0.90/1.08             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.08  thf('28', plain,
% 0.90/1.08      (![X45 : $i, X46 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 0.90/1.08          | ((k2_pre_topc @ X46 @ X45)
% 0.90/1.08              = (k4_subset_1 @ (u1_struct_0 @ X46) @ X45 @ 
% 0.90/1.08                 (k2_tops_1 @ X46 @ X45)))
% 0.90/1.08          | ~ (l1_pre_topc @ X46))),
% 0.90/1.08      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.90/1.08  thf('29', plain,
% 0.90/1.08      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.08        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.90/1.08            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.90/1.08               (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['27', '28'])).
% 0.90/1.08  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.90/1.08  thf('32', plain,
% 0.90/1.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf(t102_tops_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( l1_pre_topc @ A ) =>
% 0.90/1.08       ( ![B:$i]:
% 0.90/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.90/1.08           ( ( v5_tops_1 @ B @ A ) =>
% 0.90/1.08             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.90/1.08               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.90/1.08  thf('33', plain,
% 0.90/1.08      (![X43 : $i, X44 : $i]:
% 0.90/1.08         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.90/1.08          | ((k2_tops_1 @ X44 @ (k1_tops_1 @ X44 @ X43))
% 0.90/1.08              = (k2_tops_1 @ X44 @ X43))
% 0.90/1.08          | ~ (v5_tops_1 @ X43 @ X44)
% 0.90/1.08          | ~ (l1_pre_topc @ X44))),
% 0.90/1.08      inference('cnf', [status(esa)], [t102_tops_1])).
% 0.90/1.08  thf('34', plain,
% 0.90/1.08      ((~ (l1_pre_topc @ sk_A)
% 0.90/1.08        | ~ (v5_tops_1 @ sk_B @ sk_A)
% 0.90/1.08        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.90/1.08            = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['32', '33'])).
% 0.90/1.08  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('36', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('37', plain,
% 0.90/1.08      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.90/1.08         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.90/1.08      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.90/1.08  thf('38', plain,
% 0.90/1.08      (((sk_B)
% 0.90/1.08         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.90/1.08            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('demod', [status(thm)], ['29', '30', '31', '37'])).
% 0.90/1.08  thf('39', plain,
% 0.90/1.08      (((sk_B)
% 0.90/1.08         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.90/1.08      inference('sup+', [status(thm)], ['26', '38'])).
% 0.90/1.08  thf(t7_xboole_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.90/1.08  thf('40', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.90/1.08  thf('41', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.90/1.08      inference('sup+', [status(thm)], ['39', '40'])).
% 0.90/1.08  thf('42', plain, ($false), inference('demod', [status(thm)], ['7', '41'])).
% 0.90/1.08  
% 0.90/1.08  % SZS output end Refutation
% 0.90/1.08  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
