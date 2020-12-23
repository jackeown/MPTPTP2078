%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yEVzoICpkJ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:50 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 160 expanded)
%              Number of leaves         :   22 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  518 (1933 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v5_tops_1 @ X8 @ X9 )
      | ( X8
        = ( k2_pre_topc @ X9 @ ( k1_tops_1 @ X9 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 @ ( k2_tops_1 @ X15 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( k2_pre_topc @ X6 @ ( k2_pre_topc @ X6 @ X7 ) )
        = ( k2_pre_topc @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('18',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('22',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('23',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) )
      | ( ( k4_subset_1 @ X4 @ X3 @ X5 )
        = ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','23','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X17 @ ( k2_pre_topc @ X17 @ X16 ) ) @ ( k2_tops_1 @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('39',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['33','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['7','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yEVzoICpkJ
% 0.14/0.36  % Computer   : n020.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:34:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 91 iterations in 0.068s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.54  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.36/0.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.36/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.54  thf(t103_tops_1, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54           ( ( v5_tops_1 @ B @ A ) =>
% 0.36/0.54             ( r1_tarski @
% 0.36/0.54               ( k2_tops_1 @ A @ B ) @ 
% 0.36/0.54               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( l1_pre_topc @ A ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54              ( ( v5_tops_1 @ B @ A ) =>
% 0.36/0.54                ( r1_tarski @
% 0.36/0.54                  ( k2_tops_1 @ A @ B ) @ 
% 0.36/0.54                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.54          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d7_tops_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54           ( ( v5_tops_1 @ B @ A ) <=>
% 0.36/0.54             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X8 : $i, X9 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.36/0.54          | ~ (v5_tops_1 @ X8 @ X9)
% 0.36/0.54          | ((X8) = (k2_pre_topc @ X9 @ (k1_tops_1 @ X9 @ X8)))
% 0.36/0.54          | ~ (l1_pre_topc @ X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.54        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.54  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.36/0.54  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.36/0.54      inference('demod', [status(thm)], ['0', '6'])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t65_tops_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54           ( ( k2_pre_topc @ A @ B ) =
% 0.36/0.54             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.36/0.54          | ((k2_pre_topc @ X15 @ X14)
% 0.36/0.54              = (k4_subset_1 @ (u1_struct_0 @ X15) @ X14 @ 
% 0.36/0.54                 (k2_tops_1 @ X15 @ X14)))
% 0.36/0.54          | ~ (l1_pre_topc @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.54            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.54               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(dt_k1_tops_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.54       ( m1_subset_1 @
% 0.36/0.54         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i]:
% 0.36/0.54         (~ (l1_pre_topc @ X10)
% 0.36/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.36/0.54          | (m1_subset_1 @ (k1_tops_1 @ X10 @ X11) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.54  thf(projectivity_k2_pre_topc, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.54       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.36/0.54         ( k2_pre_topc @ A @ B ) ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i]:
% 0.36/0.54         (~ (l1_pre_topc @ X6)
% 0.36/0.54          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.36/0.54          | ((k2_pre_topc @ X6 @ (k2_pre_topc @ X6 @ X7))
% 0.36/0.54              = (k2_pre_topc @ X6 @ X7)))),
% 0.36/0.54      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.54          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.54         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.36/0.54  thf('23', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(dt_k2_tops_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.54       ( m1_subset_1 @
% 0.36/0.54         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i]:
% 0.36/0.54         (~ (l1_pre_topc @ X12)
% 0.36/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.36/0.54          | (m1_subset_1 @ (k2_tops_1 @ X12 @ X13) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.36/0.54      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.36/0.54          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4))
% 0.36/0.54          | ((k4_subset_1 @ X4 @ X3 @ X5) = (k2_xboole_0 @ X3 @ X5)))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.54            = (k2_xboole_0 @ sk_B @ X0))
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.54         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['28', '31'])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('demod', [status(thm)], ['10', '11', '23', '32'])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t72_tops_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( l1_pre_topc @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54           ( r1_tarski @
% 0.36/0.54             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.36/0.54             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.54          | (r1_tarski @ (k2_tops_1 @ X17 @ (k2_pre_topc @ X17 @ X16)) @ 
% 0.36/0.54             (k2_tops_1 @ X17 @ X16))
% 0.36/0.54          | ~ (l1_pre_topc @ X17))),
% 0.36/0.54      inference('cnf', [status(esa)], [t72_tops_1])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.54        | (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.36/0.54           (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.54  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('38', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.36/0.54  thf(t10_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.54          (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.54  thf('42', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.36/0.54      inference('sup+', [status(thm)], ['33', '41'])).
% 0.36/0.54  thf('43', plain, ($false), inference('demod', [status(thm)], ['7', '42'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
