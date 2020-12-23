%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.28Nb0WqrEP

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:46 EST 2020

% Result     : Theorem 5.79s
% Output     : Refutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 133 expanded)
%              Number of leaves         :   23 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  537 (1541 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
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

thf('27',plain,
    ( sk_B
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','26'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X19 @ ( k2_pre_topc @ X19 @ X18 ) ) @ ( k2_tops_1 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('36',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['27','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['7','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.28Nb0WqrEP
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:49:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.79/6.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.79/6.05  % Solved by: fo/fo7.sh
% 5.79/6.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.79/6.05  % done 2889 iterations in 5.589s
% 5.79/6.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.79/6.05  % SZS output start Refutation
% 5.79/6.05  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.79/6.05  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.79/6.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.79/6.05  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.79/6.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.79/6.05  thf(sk_B_type, type, sk_B: $i).
% 5.79/6.05  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 5.79/6.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.79/6.05  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 5.79/6.05  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 5.79/6.05  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 5.79/6.05  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.79/6.05  thf(sk_A_type, type, sk_A: $i).
% 5.79/6.05  thf(t103_tops_1, conjecture,
% 5.79/6.05    (![A:$i]:
% 5.79/6.05     ( ( l1_pre_topc @ A ) =>
% 5.79/6.05       ( ![B:$i]:
% 5.79/6.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.79/6.05           ( ( v5_tops_1 @ B @ A ) =>
% 5.79/6.05             ( r1_tarski @
% 5.79/6.05               ( k2_tops_1 @ A @ B ) @ 
% 5.79/6.05               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 5.79/6.05  thf(zf_stmt_0, negated_conjecture,
% 5.79/6.05    (~( ![A:$i]:
% 5.79/6.05        ( ( l1_pre_topc @ A ) =>
% 5.79/6.05          ( ![B:$i]:
% 5.79/6.05            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.79/6.05              ( ( v5_tops_1 @ B @ A ) =>
% 5.79/6.05                ( r1_tarski @
% 5.79/6.05                  ( k2_tops_1 @ A @ B ) @ 
% 5.79/6.05                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 5.79/6.05    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 5.79/6.05  thf('0', plain,
% 5.79/6.05      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.05  thf('1', plain,
% 5.79/6.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.05  thf(d7_tops_1, axiom,
% 5.79/6.05    (![A:$i]:
% 5.79/6.05     ( ( l1_pre_topc @ A ) =>
% 5.79/6.05       ( ![B:$i]:
% 5.79/6.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.79/6.05           ( ( v5_tops_1 @ B @ A ) <=>
% 5.79/6.05             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 5.79/6.05  thf('2', plain,
% 5.79/6.05      (![X10 : $i, X11 : $i]:
% 5.79/6.05         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 5.79/6.05          | ~ (v5_tops_1 @ X10 @ X11)
% 5.79/6.05          | ((X10) = (k2_pre_topc @ X11 @ (k1_tops_1 @ X11 @ X10)))
% 5.79/6.05          | ~ (l1_pre_topc @ X11))),
% 5.79/6.05      inference('cnf', [status(esa)], [d7_tops_1])).
% 5.79/6.05  thf('3', plain,
% 5.79/6.05      ((~ (l1_pre_topc @ sk_A)
% 5.79/6.05        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 5.79/6.05        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 5.79/6.05      inference('sup-', [status(thm)], ['1', '2'])).
% 5.79/6.05  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 5.79/6.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.05  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 5.79/6.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.05  thf('6', plain,
% 5.79/6.05      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.05      inference('demod', [status(thm)], ['3', '4', '5'])).
% 5.79/6.05  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.79/6.05      inference('demod', [status(thm)], ['0', '6'])).
% 5.79/6.05  thf('8', plain,
% 5.79/6.05      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.05  thf(dt_k1_tops_1, axiom,
% 5.79/6.05    (![A:$i,B:$i]:
% 5.79/6.05     ( ( ( l1_pre_topc @ A ) & 
% 5.79/6.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.79/6.05       ( m1_subset_1 @
% 5.79/6.05         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.79/6.05  thf('9', plain,
% 5.79/6.05      (![X12 : $i, X13 : $i]:
% 5.79/6.05         (~ (l1_pre_topc @ X12)
% 5.79/6.05          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 5.79/6.05          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 5.79/6.05             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 5.79/6.05      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 5.79/6.05  thf('10', plain,
% 5.79/6.05      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.79/6.05        | ~ (l1_pre_topc @ sk_A))),
% 5.79/6.05      inference('sup-', [status(thm)], ['8', '9'])).
% 5.79/6.05  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 5.79/6.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.05  thf('12', plain,
% 5.79/6.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.05      inference('demod', [status(thm)], ['10', '11'])).
% 5.79/6.05  thf(dt_k2_tops_1, axiom,
% 5.79/6.05    (![A:$i,B:$i]:
% 5.79/6.05     ( ( ( l1_pre_topc @ A ) & 
% 5.79/6.05         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.79/6.05       ( m1_subset_1 @
% 5.79/6.05         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.79/6.05  thf('13', plain,
% 5.79/6.05      (![X14 : $i, X15 : $i]:
% 5.79/6.05         (~ (l1_pre_topc @ X14)
% 5.79/6.05          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.79/6.05          | (m1_subset_1 @ (k2_tops_1 @ X14 @ X15) @ 
% 5.79/6.05             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 5.79/6.05      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 5.79/6.05  thf('14', plain,
% 5.79/6.05      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 5.79/6.05         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.79/6.05        | ~ (l1_pre_topc @ sk_A))),
% 5.79/6.05      inference('sup-', [status(thm)], ['12', '13'])).
% 5.79/6.05  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 5.79/6.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.05  thf('16', plain,
% 5.79/6.05      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 5.79/6.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.05      inference('demod', [status(thm)], ['14', '15'])).
% 5.79/6.05  thf('17', plain,
% 5.79/6.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.05      inference('demod', [status(thm)], ['10', '11'])).
% 5.79/6.05  thf(redefinition_k4_subset_1, axiom,
% 5.79/6.05    (![A:$i,B:$i,C:$i]:
% 5.79/6.05     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 5.79/6.05         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 5.79/6.05       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 5.79/6.05  thf('18', plain,
% 5.79/6.05      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.79/6.05         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 5.79/6.05          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 5.79/6.05          | ((k4_subset_1 @ X8 @ X7 @ X9) = (k2_xboole_0 @ X7 @ X9)))),
% 5.79/6.05      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 5.79/6.05  thf('19', plain,
% 5.79/6.05      (![X0 : $i]:
% 5.79/6.05         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 5.79/6.05            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 5.79/6.05          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.79/6.05      inference('sup-', [status(thm)], ['17', '18'])).
% 5.79/6.05  thf('20', plain,
% 5.79/6.05      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05         (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 5.79/6.05         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.79/6.05      inference('sup-', [status(thm)], ['16', '19'])).
% 5.79/6.05  thf('21', plain,
% 5.79/6.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.05      inference('demod', [status(thm)], ['10', '11'])).
% 5.79/6.05  thf(t65_tops_1, axiom,
% 5.79/6.05    (![A:$i]:
% 5.79/6.05     ( ( l1_pre_topc @ A ) =>
% 5.79/6.05       ( ![B:$i]:
% 5.79/6.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.79/6.05           ( ( k2_pre_topc @ A @ B ) =
% 5.79/6.05             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 5.79/6.05  thf('22', plain,
% 5.79/6.05      (![X16 : $i, X17 : $i]:
% 5.79/6.05         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 5.79/6.05          | ((k2_pre_topc @ X17 @ X16)
% 5.79/6.05              = (k4_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 5.79/6.05                 (k2_tops_1 @ X17 @ X16)))
% 5.79/6.05          | ~ (l1_pre_topc @ X17))),
% 5.79/6.05      inference('cnf', [status(esa)], [t65_tops_1])).
% 5.79/6.05  thf('23', plain,
% 5.79/6.05      ((~ (l1_pre_topc @ sk_A)
% 5.79/6.05        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 5.79/6.05            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.79/6.05               (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 5.79/6.05      inference('sup-', [status(thm)], ['21', '22'])).
% 5.79/6.05  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 5.79/6.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.05  thf('25', plain,
% 5.79/6.05      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.05      inference('demod', [status(thm)], ['3', '4', '5'])).
% 5.79/6.05  thf('26', plain,
% 5.79/6.05      (((sk_B)
% 5.79/6.05         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.79/6.05      inference('demod', [status(thm)], ['23', '24', '25'])).
% 5.79/6.05  thf('27', plain,
% 5.79/6.05      (((sk_B)
% 5.79/6.05         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05            (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.79/6.05      inference('sup+', [status(thm)], ['20', '26'])).
% 5.79/6.05  thf(commutativity_k2_xboole_0, axiom,
% 5.79/6.05    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 5.79/6.05  thf('28', plain,
% 5.79/6.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.79/6.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 5.79/6.05  thf(t7_xboole_1, axiom,
% 5.79/6.05    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.79/6.05  thf('29', plain,
% 5.79/6.05      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 5.79/6.05      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.79/6.05  thf('30', plain,
% 5.79/6.05      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.79/6.05      inference('sup+', [status(thm)], ['28', '29'])).
% 5.79/6.05  thf('31', plain,
% 5.79/6.05      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.79/6.05      inference('demod', [status(thm)], ['10', '11'])).
% 5.79/6.05  thf(t72_tops_1, axiom,
% 5.79/6.05    (![A:$i]:
% 5.79/6.05     ( ( l1_pre_topc @ A ) =>
% 5.79/6.05       ( ![B:$i]:
% 5.79/6.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.79/6.05           ( r1_tarski @
% 5.79/6.05             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 5.79/6.05             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 5.79/6.05  thf('32', plain,
% 5.79/6.05      (![X18 : $i, X19 : $i]:
% 5.79/6.05         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 5.79/6.05          | (r1_tarski @ (k2_tops_1 @ X19 @ (k2_pre_topc @ X19 @ X18)) @ 
% 5.79/6.05             (k2_tops_1 @ X19 @ X18))
% 5.79/6.05          | ~ (l1_pre_topc @ X19))),
% 5.79/6.05      inference('cnf', [status(esa)], [t72_tops_1])).
% 5.79/6.05  thf('33', plain,
% 5.79/6.05      ((~ (l1_pre_topc @ sk_A)
% 5.79/6.05        | (r1_tarski @ 
% 5.79/6.05           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 5.79/6.05           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.79/6.05      inference('sup-', [status(thm)], ['31', '32'])).
% 5.79/6.05  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 5.79/6.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.79/6.05  thf('35', plain,
% 5.79/6.05      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.05      inference('demod', [status(thm)], ['3', '4', '5'])).
% 5.79/6.05  thf('36', plain,
% 5.79/6.05      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 5.79/6.05      inference('demod', [status(thm)], ['33', '34', '35'])).
% 5.79/6.05  thf(t1_xboole_1, axiom,
% 5.79/6.05    (![A:$i,B:$i,C:$i]:
% 5.79/6.05     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 5.79/6.05       ( r1_tarski @ A @ C ) ))).
% 5.79/6.05  thf('37', plain,
% 5.79/6.05      (![X2 : $i, X3 : $i, X4 : $i]:
% 5.79/6.05         (~ (r1_tarski @ X2 @ X3)
% 5.79/6.05          | ~ (r1_tarski @ X3 @ X4)
% 5.79/6.05          | (r1_tarski @ X2 @ X4))),
% 5.79/6.05      inference('cnf', [status(esa)], [t1_xboole_1])).
% 5.79/6.05  thf('38', plain,
% 5.79/6.05      (![X0 : $i]:
% 5.79/6.05         ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 5.79/6.05          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 5.79/6.05      inference('sup-', [status(thm)], ['36', '37'])).
% 5.79/6.05  thf('39', plain,
% 5.79/6.05      (![X0 : $i]:
% 5.79/6.05         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 5.79/6.05          (k2_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 5.79/6.05      inference('sup-', [status(thm)], ['30', '38'])).
% 5.79/6.05  thf('40', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 5.79/6.05      inference('sup+', [status(thm)], ['27', '39'])).
% 5.79/6.05  thf('41', plain, ($false), inference('demod', [status(thm)], ['7', '40'])).
% 5.79/6.05  
% 5.79/6.05  % SZS output end Refutation
% 5.79/6.05  
% 5.79/6.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
