%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R8DlvJO8jC

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:50 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 106 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :  487 (1195 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) )
      | ( ( k4_subset_1 @ X6 @ X5 @ X7 )
        = ( k2_xboole_0 @ X5 @ X7 ) ) ) ),
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

thf('26',plain,(
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

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_tops_1 @ X15 @ ( k1_tops_1 @ X15 @ X14 ) )
        = ( k2_tops_1 @ X15 @ X14 ) )
      | ~ ( v5_tops_1 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t102_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25','31'])).

thf('33',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['20','32'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['7','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R8DlvJO8jC
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:54:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 143 iterations in 0.343s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.80  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.59/0.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.80  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.59/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.80  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.59/0.80  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.59/0.80  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.59/0.80  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.80  thf(t103_tops_1, conjecture,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( l1_pre_topc @ A ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80           ( ( v5_tops_1 @ B @ A ) =>
% 0.59/0.80             ( r1_tarski @
% 0.59/0.80               ( k2_tops_1 @ A @ B ) @ 
% 0.59/0.80               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.80    (~( ![A:$i]:
% 0.59/0.80        ( ( l1_pre_topc @ A ) =>
% 0.59/0.80          ( ![B:$i]:
% 0.59/0.80            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80              ( ( v5_tops_1 @ B @ A ) =>
% 0.59/0.80                ( r1_tarski @
% 0.59/0.80                  ( k2_tops_1 @ A @ B ) @ 
% 0.59/0.80                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 0.59/0.80  thf('0', plain,
% 0.59/0.80      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.80          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('1', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(d7_tops_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( l1_pre_topc @ A ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80           ( ( v5_tops_1 @ B @ A ) <=>
% 0.59/0.80             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.59/0.80  thf('2', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.59/0.80          | ~ (v5_tops_1 @ X8 @ X9)
% 0.59/0.80          | ((X8) = (k2_pre_topc @ X9 @ (k1_tops_1 @ X9 @ X8)))
% 0.59/0.80          | ~ (l1_pre_topc @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.59/0.80        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.80  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.59/0.80  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.59/0.80      inference('demod', [status(thm)], ['0', '6'])).
% 0.59/0.80  thf('8', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(dt_k2_tops_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( l1_pre_topc @ A ) & 
% 0.59/0.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.80       ( m1_subset_1 @
% 0.59/0.80         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.80  thf('9', plain,
% 0.59/0.80      (![X12 : $i, X13 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X12)
% 0.59/0.80          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.59/0.80          | (m1_subset_1 @ (k2_tops_1 @ X12 @ X13) @ 
% 0.59/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.80         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.80  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(dt_k1_tops_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ( l1_pre_topc @ A ) & 
% 0.59/0.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.80       ( m1_subset_1 @
% 0.59/0.80         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      (![X10 : $i, X11 : $i]:
% 0.59/0.80         (~ (l1_pre_topc @ X10)
% 0.59/0.80          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.59/0.80          | (m1_subset_1 @ (k1_tops_1 @ X10 @ X11) @ 
% 0.59/0.80             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.80         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.80        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.80  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['15', '16'])).
% 0.59/0.80  thf(redefinition_k4_subset_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.59/0.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.80       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.59/0.80          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6))
% 0.59/0.80          | ((k4_subset_1 @ X6 @ X5 @ X7) = (k2_xboole_0 @ X5 @ X7)))),
% 0.59/0.80      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.59/0.80            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.80         (k2_tops_1 @ sk_A @ sk_B))
% 0.59/0.80         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['12', '19'])).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['15', '16'])).
% 0.59/0.80  thf(t65_tops_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( l1_pre_topc @ A ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80           ( ( k2_pre_topc @ A @ B ) =
% 0.59/0.80             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.59/0.80  thf('22', plain,
% 0.59/0.80      (![X16 : $i, X17 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.59/0.80          | ((k2_pre_topc @ X17 @ X16)
% 0.59/0.80              = (k4_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 0.59/0.80                 (k2_tops_1 @ X17 @ X16)))
% 0.59/0.80          | ~ (l1_pre_topc @ X17))),
% 0.59/0.80      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.59/0.80            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.80               (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.80               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['21', '22'])).
% 0.59/0.80  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(t102_tops_1, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( l1_pre_topc @ A ) =>
% 0.59/0.80       ( ![B:$i]:
% 0.59/0.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.80           ( ( v5_tops_1 @ B @ A ) =>
% 0.59/0.80             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.59/0.80               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.59/0.80  thf('27', plain,
% 0.59/0.80      (![X14 : $i, X15 : $i]:
% 0.59/0.80         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.59/0.80          | ((k2_tops_1 @ X15 @ (k1_tops_1 @ X15 @ X14))
% 0.59/0.80              = (k2_tops_1 @ X15 @ X14))
% 0.59/0.80          | ~ (v5_tops_1 @ X14 @ X15)
% 0.59/0.80          | ~ (l1_pre_topc @ X15))),
% 0.59/0.80      inference('cnf', [status(esa)], [t102_tops_1])).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.80        | ~ (v5_tops_1 @ sk_B @ sk_A)
% 0.59/0.80        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.59/0.80            = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.80  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('30', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.59/0.80         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (((sk_B)
% 0.59/0.80         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.80            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('demod', [status(thm)], ['23', '24', '25', '31'])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (((sk_B)
% 0.59/0.80         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['20', '32'])).
% 0.59/0.80  thf(t36_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.59/0.80      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.59/0.80  thf(t44_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.59/0.80       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.80  thf('35', plain,
% 0.59/0.80      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.80         ((r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4))
% 0.59/0.80          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.59/0.80  thf('36', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.80  thf('37', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.59/0.80      inference('sup+', [status(thm)], ['33', '36'])).
% 0.59/0.80  thf('38', plain, ($false), inference('demod', [status(thm)], ['7', '37'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
