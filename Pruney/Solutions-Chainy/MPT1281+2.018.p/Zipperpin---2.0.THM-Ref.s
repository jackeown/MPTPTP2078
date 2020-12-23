%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h7Yffdr15o

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:47 EST 2020

% Result     : Theorem 10.41s
% Output     : Refutation 10.41s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 127 expanded)
%              Number of leaves         :   22 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  566 (1514 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v5_tops_1 @ X23 @ X24 )
      | ( X23
        = ( k2_pre_topc @ X24 @ ( k1_tops_1 @ X24 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_subset_1 @ X13 @ X14 @ X12 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X32 ) @ X31 @ ( k2_tops_1 @ X32 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_tops_1 @ X30 @ ( k1_tops_1 @ X30 @ X29 ) )
        = ( k2_tops_1 @ X30 @ X29 ) )
      | ~ ( v5_tops_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['7','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h7Yffdr15o
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 10.41/10.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.41/10.64  % Solved by: fo/fo7.sh
% 10.41/10.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.41/10.64  % done 21242 iterations in 10.182s
% 10.41/10.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.41/10.64  % SZS output start Refutation
% 10.41/10.64  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 10.41/10.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.41/10.64  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 10.41/10.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.41/10.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 10.41/10.64  thf(sk_A_type, type, sk_A: $i).
% 10.41/10.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.41/10.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 10.41/10.64  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 10.41/10.64  thf(sk_B_type, type, sk_B: $i).
% 10.41/10.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.41/10.64  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 10.41/10.64  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 10.41/10.64  thf(t103_tops_1, conjecture,
% 10.41/10.64    (![A:$i]:
% 10.41/10.64     ( ( l1_pre_topc @ A ) =>
% 10.41/10.64       ( ![B:$i]:
% 10.41/10.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.41/10.64           ( ( v5_tops_1 @ B @ A ) =>
% 10.41/10.64             ( r1_tarski @
% 10.41/10.64               ( k2_tops_1 @ A @ B ) @ 
% 10.41/10.64               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 10.41/10.64  thf(zf_stmt_0, negated_conjecture,
% 10.41/10.64    (~( ![A:$i]:
% 10.41/10.64        ( ( l1_pre_topc @ A ) =>
% 10.41/10.64          ( ![B:$i]:
% 10.41/10.64            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.41/10.64              ( ( v5_tops_1 @ B @ A ) =>
% 10.41/10.64                ( r1_tarski @
% 10.41/10.64                  ( k2_tops_1 @ A @ B ) @ 
% 10.41/10.64                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 10.41/10.64    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 10.41/10.64  thf('0', plain,
% 10.41/10.64      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf('1', plain,
% 10.41/10.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf(d7_tops_1, axiom,
% 10.41/10.64    (![A:$i]:
% 10.41/10.64     ( ( l1_pre_topc @ A ) =>
% 10.41/10.64       ( ![B:$i]:
% 10.41/10.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.41/10.64           ( ( v5_tops_1 @ B @ A ) <=>
% 10.41/10.64             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 10.41/10.64  thf('2', plain,
% 10.41/10.64      (![X23 : $i, X24 : $i]:
% 10.41/10.64         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 10.41/10.64          | ~ (v5_tops_1 @ X23 @ X24)
% 10.41/10.64          | ((X23) = (k2_pre_topc @ X24 @ (k1_tops_1 @ X24 @ X23)))
% 10.41/10.64          | ~ (l1_pre_topc @ X24))),
% 10.41/10.64      inference('cnf', [status(esa)], [d7_tops_1])).
% 10.41/10.64  thf('3', plain,
% 10.41/10.64      ((~ (l1_pre_topc @ sk_A)
% 10.41/10.64        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 10.41/10.64        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 10.41/10.64      inference('sup-', [status(thm)], ['1', '2'])).
% 10.41/10.64  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf('6', plain,
% 10.41/10.64      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.41/10.64      inference('demod', [status(thm)], ['3', '4', '5'])).
% 10.41/10.64  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 10.41/10.64      inference('demod', [status(thm)], ['0', '6'])).
% 10.41/10.64  thf('8', plain,
% 10.41/10.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf(dt_k2_tops_1, axiom,
% 10.41/10.64    (![A:$i,B:$i]:
% 10.41/10.64     ( ( ( l1_pre_topc @ A ) & 
% 10.41/10.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.41/10.64       ( m1_subset_1 @
% 10.41/10.64         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 10.41/10.64  thf('9', plain,
% 10.41/10.64      (![X27 : $i, X28 : $i]:
% 10.41/10.64         (~ (l1_pre_topc @ X27)
% 10.41/10.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 10.41/10.64          | (m1_subset_1 @ (k2_tops_1 @ X27 @ X28) @ 
% 10.41/10.64             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 10.41/10.64      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 10.41/10.64  thf('10', plain,
% 10.41/10.64      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.41/10.64        | ~ (l1_pre_topc @ sk_A))),
% 10.41/10.64      inference('sup-', [status(thm)], ['8', '9'])).
% 10.41/10.64  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf('12', plain,
% 10.41/10.64      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.41/10.64      inference('demod', [status(thm)], ['10', '11'])).
% 10.41/10.64  thf('13', plain,
% 10.41/10.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf(dt_k1_tops_1, axiom,
% 10.41/10.64    (![A:$i,B:$i]:
% 10.41/10.64     ( ( ( l1_pre_topc @ A ) & 
% 10.41/10.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.41/10.64       ( m1_subset_1 @
% 10.41/10.64         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 10.41/10.64  thf('14', plain,
% 10.41/10.64      (![X25 : $i, X26 : $i]:
% 10.41/10.64         (~ (l1_pre_topc @ X25)
% 10.41/10.64          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 10.41/10.64          | (m1_subset_1 @ (k1_tops_1 @ X25 @ X26) @ 
% 10.41/10.64             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 10.41/10.64      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 10.41/10.64  thf('15', plain,
% 10.41/10.64      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.41/10.64        | ~ (l1_pre_topc @ sk_A))),
% 10.41/10.64      inference('sup-', [status(thm)], ['13', '14'])).
% 10.41/10.64  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf('17', plain,
% 10.41/10.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.41/10.64      inference('demod', [status(thm)], ['15', '16'])).
% 10.41/10.64  thf(commutativity_k4_subset_1, axiom,
% 10.41/10.64    (![A:$i,B:$i,C:$i]:
% 10.41/10.64     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 10.41/10.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 10.41/10.64       ( ( k4_subset_1 @ A @ B @ C ) = ( k4_subset_1 @ A @ C @ B ) ) ))).
% 10.41/10.64  thf('18', plain,
% 10.41/10.64      (![X12 : $i, X13 : $i, X14 : $i]:
% 10.41/10.64         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 10.41/10.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 10.41/10.64          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k4_subset_1 @ X13 @ X14 @ X12)))),
% 10.41/10.64      inference('cnf', [status(esa)], [commutativity_k4_subset_1])).
% 10.41/10.64  thf('19', plain,
% 10.41/10.64      (![X0 : $i]:
% 10.41/10.64         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 10.41/10.64            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 10.41/10.64               (k1_tops_1 @ sk_A @ sk_B)))
% 10.41/10.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 10.41/10.64      inference('sup-', [status(thm)], ['17', '18'])).
% 10.41/10.64  thf('20', plain,
% 10.41/10.64      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64         (k2_tops_1 @ sk_A @ sk_B))
% 10.41/10.64         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64            (k1_tops_1 @ sk_A @ sk_B)))),
% 10.41/10.64      inference('sup-', [status(thm)], ['12', '19'])).
% 10.41/10.64  thf('21', plain,
% 10.41/10.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.41/10.64      inference('demod', [status(thm)], ['15', '16'])).
% 10.41/10.64  thf('22', plain,
% 10.41/10.64      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.41/10.64      inference('demod', [status(thm)], ['10', '11'])).
% 10.41/10.64  thf(redefinition_k4_subset_1, axiom,
% 10.41/10.64    (![A:$i,B:$i,C:$i]:
% 10.41/10.64     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 10.41/10.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 10.41/10.64       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 10.41/10.64  thf('23', plain,
% 10.41/10.64      (![X15 : $i, X16 : $i, X17 : $i]:
% 10.41/10.64         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 10.41/10.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 10.41/10.64          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 10.41/10.64      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 10.41/10.64  thf('24', plain,
% 10.41/10.64      (![X0 : $i]:
% 10.41/10.64         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 10.41/10.64            = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0))
% 10.41/10.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 10.41/10.64      inference('sup-', [status(thm)], ['22', '23'])).
% 10.41/10.64  thf('25', plain,
% 10.41/10.64      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64         (k1_tops_1 @ sk_A @ sk_B))
% 10.41/10.64         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.41/10.64      inference('sup-', [status(thm)], ['21', '24'])).
% 10.41/10.64  thf('26', plain,
% 10.41/10.64      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64         (k2_tops_1 @ sk_A @ sk_B))
% 10.41/10.64         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.41/10.64      inference('demod', [status(thm)], ['20', '25'])).
% 10.41/10.64  thf('27', plain,
% 10.41/10.64      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.41/10.64      inference('demod', [status(thm)], ['15', '16'])).
% 10.41/10.64  thf(t65_tops_1, axiom,
% 10.41/10.64    (![A:$i]:
% 10.41/10.64     ( ( l1_pre_topc @ A ) =>
% 10.41/10.64       ( ![B:$i]:
% 10.41/10.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.41/10.64           ( ( k2_pre_topc @ A @ B ) =
% 10.41/10.64             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 10.41/10.64  thf('28', plain,
% 10.41/10.64      (![X31 : $i, X32 : $i]:
% 10.41/10.64         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 10.41/10.64          | ((k2_pre_topc @ X32 @ X31)
% 10.41/10.64              = (k4_subset_1 @ (u1_struct_0 @ X32) @ X31 @ 
% 10.41/10.64                 (k2_tops_1 @ X32 @ X31)))
% 10.41/10.64          | ~ (l1_pre_topc @ X32))),
% 10.41/10.64      inference('cnf', [status(esa)], [t65_tops_1])).
% 10.41/10.64  thf('29', plain,
% 10.41/10.64      ((~ (l1_pre_topc @ sk_A)
% 10.41/10.64        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 10.41/10.64            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 10.41/10.64               (k1_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 10.41/10.64      inference('sup-', [status(thm)], ['27', '28'])).
% 10.41/10.64  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf('31', plain,
% 10.41/10.64      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.41/10.64      inference('demod', [status(thm)], ['3', '4', '5'])).
% 10.41/10.64  thf('32', plain,
% 10.41/10.64      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf(t102_tops_1, axiom,
% 10.41/10.64    (![A:$i]:
% 10.41/10.64     ( ( l1_pre_topc @ A ) =>
% 10.41/10.64       ( ![B:$i]:
% 10.41/10.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.41/10.64           ( ( v5_tops_1 @ B @ A ) =>
% 10.41/10.64             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 10.41/10.64               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 10.41/10.64  thf('33', plain,
% 10.41/10.64      (![X29 : $i, X30 : $i]:
% 10.41/10.64         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 10.41/10.64          | ((k2_tops_1 @ X30 @ (k1_tops_1 @ X30 @ X29))
% 10.41/10.64              = (k2_tops_1 @ X30 @ X29))
% 10.41/10.64          | ~ (v5_tops_1 @ X29 @ X30)
% 10.41/10.64          | ~ (l1_pre_topc @ X30))),
% 10.41/10.64      inference('cnf', [status(esa)], [t102_tops_1])).
% 10.41/10.64  thf('34', plain,
% 10.41/10.64      ((~ (l1_pre_topc @ sk_A)
% 10.41/10.64        | ~ (v5_tops_1 @ sk_B @ sk_A)
% 10.41/10.64        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 10.41/10.64            = (k2_tops_1 @ sk_A @ sk_B)))),
% 10.41/10.64      inference('sup-', [status(thm)], ['32', '33'])).
% 10.41/10.64  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf('36', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 10.41/10.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.41/10.64  thf('37', plain,
% 10.41/10.64      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 10.41/10.64         = (k2_tops_1 @ sk_A @ sk_B))),
% 10.41/10.64      inference('demod', [status(thm)], ['34', '35', '36'])).
% 10.41/10.64  thf('38', plain,
% 10.41/10.64      (((sk_B)
% 10.41/10.64         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 10.41/10.64            (k2_tops_1 @ sk_A @ sk_B)))),
% 10.41/10.64      inference('demod', [status(thm)], ['29', '30', '31', '37'])).
% 10.41/10.64  thf('39', plain,
% 10.41/10.64      (((sk_B)
% 10.41/10.64         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 10.41/10.64      inference('sup+', [status(thm)], ['26', '38'])).
% 10.41/10.64  thf(t7_xboole_1, axiom,
% 10.41/10.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 10.41/10.64  thf('40', plain,
% 10.41/10.64      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 10.41/10.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 10.41/10.64  thf('41', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 10.41/10.64      inference('sup+', [status(thm)], ['39', '40'])).
% 10.41/10.64  thf('42', plain, ($false), inference('demod', [status(thm)], ['7', '41'])).
% 10.41/10.64  
% 10.41/10.64  % SZS output end Refutation
% 10.41/10.64  
% 10.41/10.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
