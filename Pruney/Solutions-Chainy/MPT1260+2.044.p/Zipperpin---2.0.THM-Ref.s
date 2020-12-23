%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xjHzzpxTk6

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:29 EST 2020

% Result     : Theorem 4.09s
% Output     : Refutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 736 expanded)
%              Number of leaves         :   44 ( 236 expanded)
%              Depth                    :   24
%              Number of atoms          : 1841 (8285 expanded)
%              Number of equality atoms :  118 ( 411 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( r1_tarski @ X54 @ ( k2_pre_topc @ X55 @ X54 ) )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k2_tops_1 @ X59 @ X58 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X59 ) @ ( k2_pre_topc @ X59 @ X58 ) @ ( k1_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X52 @ X53 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X65: $i,X66: $i] :
      ( ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X66 ) ) )
      | ( ( k1_tops_1 @ X66 @ X65 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X66 ) @ X65 @ ( k2_tops_1 @ X66 @ X65 ) ) )
      | ~ ( l1_pre_topc @ X66 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

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

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X60: $i,X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( v3_pre_topc @ X60 @ X61 )
      | ~ ( r1_tarski @ X60 @ X62 )
      | ( r1_tarski @ X60 @ ( k1_tops_1 @ X61 @ X62 ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X19 @ X21 @ X20 )
        = ( k9_subset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X0 )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k9_subset_1 @ X41 @ X39 @ X40 )
        = ( k3_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X0 )
      = ( k3_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X0 )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X46: $i,X47: $i] :
      ( ( r1_tarski @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('63',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k9_subset_1 @ X41 @ X39 @ X40 )
        = ( k3_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ X1 @ sk_B )
      = ( k3_xboole_0 @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['57','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('73',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('74',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('76',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('79',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X44 @ X42 )
        = ( k9_subset_1 @ X43 @ X44 @ ( k3_subset_1 @ X43 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      | ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ sk_B )
    = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('83',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('85',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X25 ) @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('86',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = X22 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('87',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('90',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('91',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X35 @ ( k3_subset_1 @ X35 @ X34 ) )
        = X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('94',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('96',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('100',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k9_subset_1 @ X19 @ X21 @ X20 )
        = ( k9_subset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('103',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k9_subset_1 @ X41 @ X39 @ X40 )
        = ( k3_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('106',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['81','84','89','98','105'])).

thf('107',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['76','106'])).

thf('108',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['71','107'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('109',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('110',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('111',plain,(
    ! [X46: $i,X48: $i] :
      ( ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X48 ) )
      | ~ ( r1_tarski @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('117',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X35 @ ( k3_subset_1 @ X35 @ X34 ) )
        = X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('120',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X23 @ X24 )
        = ( k4_xboole_0 @ X23 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['118','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['115','124'])).

thf('126',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('127',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k7_subset_1 @ X37 @ X36 @ X38 )
        = ( k4_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['125','128'])).

thf('130',plain,
    ( ( ( k7_subset_1 @ sk_B @ sk_B @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['108','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('132',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','133'])).

thf('135',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('136',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('138',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( l1_pre_topc @ X56 )
      | ~ ( v2_pre_topc @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X56 @ X57 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('139',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['136','142'])).

thf('144',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('145',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['43'])).

thf('147',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['46','145','146'])).

thf('148',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['44','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['42','148'])).

thf('150',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','149'])).

thf('151',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('152',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['150','153'])).

thf('155',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','154'])).

thf('156',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['21','155'])).

thf('157',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['8','156'])).

thf('158',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['45'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('160',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('161',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['46','145'])).

thf('163',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['161','162'])).

thf('164',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['157','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xjHzzpxTk6
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.09/4.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.09/4.29  % Solved by: fo/fo7.sh
% 4.09/4.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.09/4.29  % done 9850 iterations in 3.798s
% 4.09/4.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.09/4.29  % SZS output start Refutation
% 4.09/4.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.09/4.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.09/4.29  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 4.09/4.29  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 4.09/4.29  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 4.09/4.29  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.09/4.29  thf(sk_B_type, type, sk_B: $i).
% 4.09/4.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.09/4.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.09/4.29  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.09/4.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.09/4.29  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 4.09/4.29  thf(sk_A_type, type, sk_A: $i).
% 4.09/4.29  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.09/4.29  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 4.09/4.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.09/4.29  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.09/4.29  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 4.09/4.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.09/4.29  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 4.09/4.29  thf(t76_tops_1, conjecture,
% 4.09/4.29    (![A:$i]:
% 4.09/4.29     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.09/4.29       ( ![B:$i]:
% 4.09/4.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.09/4.29           ( ( v3_pre_topc @ B @ A ) <=>
% 4.09/4.29             ( ( k2_tops_1 @ A @ B ) =
% 4.09/4.29               ( k7_subset_1 @
% 4.09/4.29                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 4.09/4.29  thf(zf_stmt_0, negated_conjecture,
% 4.09/4.29    (~( ![A:$i]:
% 4.09/4.29        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.09/4.29          ( ![B:$i]:
% 4.09/4.29            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.09/4.29              ( ( v3_pre_topc @ B @ A ) <=>
% 4.09/4.29                ( ( k2_tops_1 @ A @ B ) =
% 4.09/4.29                  ( k7_subset_1 @
% 4.09/4.29                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 4.09/4.29    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 4.09/4.29  thf('0', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf(t48_pre_topc, axiom,
% 4.09/4.29    (![A:$i]:
% 4.09/4.29     ( ( l1_pre_topc @ A ) =>
% 4.09/4.29       ( ![B:$i]:
% 4.09/4.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.09/4.29           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 4.09/4.29  thf('1', plain,
% 4.09/4.29      (![X54 : $i, X55 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 4.09/4.29          | (r1_tarski @ X54 @ (k2_pre_topc @ X55 @ X54))
% 4.09/4.29          | ~ (l1_pre_topc @ X55))),
% 4.09/4.29      inference('cnf', [status(esa)], [t48_pre_topc])).
% 4.09/4.29  thf('2', plain,
% 4.09/4.29      ((~ (l1_pre_topc @ sk_A)
% 4.09/4.29        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['0', '1'])).
% 4.09/4.29  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('4', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 4.09/4.29      inference('demod', [status(thm)], ['2', '3'])).
% 4.09/4.29  thf(t3_subset, axiom,
% 4.09/4.29    (![A:$i,B:$i]:
% 4.09/4.29     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.09/4.29  thf('5', plain,
% 4.09/4.29      (![X46 : $i, X48 : $i]:
% 4.09/4.29         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 4.09/4.29      inference('cnf', [status(esa)], [t3_subset])).
% 4.09/4.29  thf('6', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['4', '5'])).
% 4.09/4.29  thf(d5_subset_1, axiom,
% 4.09/4.29    (![A:$i,B:$i]:
% 4.09/4.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.29       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 4.09/4.29  thf('7', plain,
% 4.09/4.29      (![X23 : $i, X24 : $i]:
% 4.09/4.29         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 4.09/4.29          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 4.09/4.29      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.09/4.29  thf('8', plain,
% 4.09/4.29      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 4.09/4.29         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 4.09/4.29      inference('sup-', [status(thm)], ['6', '7'])).
% 4.09/4.29  thf('9', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf(l78_tops_1, axiom,
% 4.09/4.29    (![A:$i]:
% 4.09/4.29     ( ( l1_pre_topc @ A ) =>
% 4.09/4.29       ( ![B:$i]:
% 4.09/4.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.09/4.29           ( ( k2_tops_1 @ A @ B ) =
% 4.09/4.29             ( k7_subset_1 @
% 4.09/4.29               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 4.09/4.29               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.09/4.29  thf('10', plain,
% 4.09/4.29      (![X58 : $i, X59 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 4.09/4.29          | ((k2_tops_1 @ X59 @ X58)
% 4.09/4.29              = (k7_subset_1 @ (u1_struct_0 @ X59) @ 
% 4.09/4.29                 (k2_pre_topc @ X59 @ X58) @ (k1_tops_1 @ X59 @ X58)))
% 4.09/4.29          | ~ (l1_pre_topc @ X59))),
% 4.09/4.29      inference('cnf', [status(esa)], [l78_tops_1])).
% 4.09/4.29  thf('11', plain,
% 4.09/4.29      ((~ (l1_pre_topc @ sk_A)
% 4.09/4.29        | ((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 4.09/4.29      inference('sup-', [status(thm)], ['9', '10'])).
% 4.09/4.29  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('13', plain,
% 4.09/4.29      (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.09/4.29            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.09/4.29      inference('demod', [status(thm)], ['11', '12'])).
% 4.09/4.29  thf('14', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf(dt_k2_pre_topc, axiom,
% 4.09/4.29    (![A:$i,B:$i]:
% 4.09/4.29     ( ( ( l1_pre_topc @ A ) & 
% 4.09/4.29         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.09/4.29       ( m1_subset_1 @
% 4.09/4.29         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.09/4.29  thf('15', plain,
% 4.09/4.29      (![X52 : $i, X53 : $i]:
% 4.09/4.29         (~ (l1_pre_topc @ X52)
% 4.09/4.29          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 4.09/4.29          | (m1_subset_1 @ (k2_pre_topc @ X52 @ X53) @ 
% 4.09/4.29             (k1_zfmisc_1 @ (u1_struct_0 @ X52))))),
% 4.09/4.29      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 4.09/4.29  thf('16', plain,
% 4.09/4.29      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.09/4.29         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.09/4.29        | ~ (l1_pre_topc @ sk_A))),
% 4.09/4.29      inference('sup-', [status(thm)], ['14', '15'])).
% 4.09/4.29  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('18', plain,
% 4.09/4.29      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.09/4.29        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('demod', [status(thm)], ['16', '17'])).
% 4.09/4.29  thf(redefinition_k7_subset_1, axiom,
% 4.09/4.29    (![A:$i,B:$i,C:$i]:
% 4.09/4.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.29       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 4.09/4.29  thf('19', plain,
% 4.09/4.29      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 4.09/4.29          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 4.09/4.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.09/4.29  thf('20', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.09/4.29           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['18', '19'])).
% 4.09/4.29  thf('21', plain,
% 4.09/4.29      (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.09/4.29            (k1_tops_1 @ sk_A @ sk_B)))),
% 4.09/4.29      inference('demod', [status(thm)], ['13', '20'])).
% 4.09/4.29  thf('22', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf(t74_tops_1, axiom,
% 4.09/4.29    (![A:$i]:
% 4.09/4.29     ( ( l1_pre_topc @ A ) =>
% 4.09/4.29       ( ![B:$i]:
% 4.09/4.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.09/4.29           ( ( k1_tops_1 @ A @ B ) =
% 4.09/4.29             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 4.09/4.29  thf('23', plain,
% 4.09/4.29      (![X65 : $i, X66 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (u1_struct_0 @ X66)))
% 4.09/4.29          | ((k1_tops_1 @ X66 @ X65)
% 4.09/4.29              = (k7_subset_1 @ (u1_struct_0 @ X66) @ X65 @ 
% 4.09/4.29                 (k2_tops_1 @ X66 @ X65)))
% 4.09/4.29          | ~ (l1_pre_topc @ X66))),
% 4.09/4.29      inference('cnf', [status(esa)], [t74_tops_1])).
% 4.09/4.29  thf('24', plain,
% 4.09/4.29      ((~ (l1_pre_topc @ sk_A)
% 4.09/4.29        | ((k1_tops_1 @ sk_A @ sk_B)
% 4.09/4.29            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 4.09/4.29               (k2_tops_1 @ sk_A @ sk_B))))),
% 4.09/4.29      inference('sup-', [status(thm)], ['22', '23'])).
% 4.09/4.29  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('26', plain,
% 4.09/4.29      (((k1_tops_1 @ sk_A @ sk_B)
% 4.09/4.29         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 4.09/4.29            (k2_tops_1 @ sk_A @ sk_B)))),
% 4.09/4.29      inference('demod', [status(thm)], ['24', '25'])).
% 4.09/4.29  thf('27', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('28', plain,
% 4.09/4.29      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 4.09/4.29          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 4.09/4.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.09/4.29  thf('29', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 4.09/4.29           = (k4_xboole_0 @ sk_B @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['27', '28'])).
% 4.09/4.29  thf('30', plain,
% 4.09/4.29      (((k1_tops_1 @ sk_A @ sk_B)
% 4.09/4.29         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.09/4.29      inference('demod', [status(thm)], ['26', '29'])).
% 4.09/4.29  thf(t36_xboole_1, axiom,
% 4.09/4.29    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.09/4.29  thf('31', plain,
% 4.09/4.29      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 4.09/4.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.09/4.29  thf(d10_xboole_0, axiom,
% 4.09/4.29    (![A:$i,B:$i]:
% 4.09/4.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.09/4.29  thf('32', plain,
% 4.09/4.29      (![X2 : $i, X4 : $i]:
% 4.09/4.29         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 4.09/4.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.09/4.29  thf('33', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.09/4.29          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['31', '32'])).
% 4.09/4.29  thf('34', plain,
% 4.09/4.29      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 4.09/4.29        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 4.09/4.29      inference('sup-', [status(thm)], ['30', '33'])).
% 4.09/4.29  thf('35', plain,
% 4.09/4.29      (((k1_tops_1 @ sk_A @ sk_B)
% 4.09/4.29         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.09/4.29      inference('demod', [status(thm)], ['26', '29'])).
% 4.09/4.29  thf('36', plain,
% 4.09/4.29      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 4.09/4.29        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 4.09/4.29      inference('demod', [status(thm)], ['34', '35'])).
% 4.09/4.29  thf('37', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('38', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf(t56_tops_1, axiom,
% 4.09/4.29    (![A:$i]:
% 4.09/4.29     ( ( l1_pre_topc @ A ) =>
% 4.09/4.29       ( ![B:$i]:
% 4.09/4.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.09/4.29           ( ![C:$i]:
% 4.09/4.29             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.09/4.29               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 4.09/4.29                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 4.09/4.29  thf('39', plain,
% 4.09/4.29      (![X60 : $i, X61 : $i, X62 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 4.09/4.29          | ~ (v3_pre_topc @ X60 @ X61)
% 4.09/4.29          | ~ (r1_tarski @ X60 @ X62)
% 4.09/4.29          | (r1_tarski @ X60 @ (k1_tops_1 @ X61 @ X62))
% 4.09/4.29          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 4.09/4.29          | ~ (l1_pre_topc @ X61))),
% 4.09/4.29      inference('cnf', [status(esa)], [t56_tops_1])).
% 4.09/4.29  thf('40', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         (~ (l1_pre_topc @ sk_A)
% 4.09/4.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.09/4.29          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 4.09/4.29          | ~ (r1_tarski @ sk_B @ X0)
% 4.09/4.29          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.09/4.29      inference('sup-', [status(thm)], ['38', '39'])).
% 4.09/4.29  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('42', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.09/4.29          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 4.09/4.29          | ~ (r1_tarski @ sk_B @ X0)
% 4.09/4.29          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.09/4.29      inference('demod', [status(thm)], ['40', '41'])).
% 4.09/4.29  thf('43', plain,
% 4.09/4.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 4.09/4.29        | (v3_pre_topc @ sk_B @ sk_A))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('44', plain,
% 4.09/4.29      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 4.09/4.29      inference('split', [status(esa)], ['43'])).
% 4.09/4.29  thf('45', plain,
% 4.09/4.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 4.09/4.29        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('46', plain,
% 4.09/4.29      (~
% 4.09/4.29       (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 4.09/4.29       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 4.09/4.29      inference('split', [status(esa)], ['45'])).
% 4.09/4.29  thf('47', plain,
% 4.09/4.29      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 4.09/4.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.09/4.29  thf(t44_xboole_1, axiom,
% 4.09/4.29    (![A:$i,B:$i,C:$i]:
% 4.09/4.29     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 4.09/4.29       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 4.09/4.29  thf('48', plain,
% 4.09/4.29      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.09/4.29         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 4.09/4.29          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 4.09/4.29      inference('cnf', [status(esa)], [t44_xboole_1])).
% 4.09/4.29  thf('49', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['47', '48'])).
% 4.09/4.29  thf('50', plain,
% 4.09/4.29      (![X46 : $i, X48 : $i]:
% 4.09/4.29         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 4.09/4.29      inference('cnf', [status(esa)], [t3_subset])).
% 4.09/4.29  thf('51', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['49', '50'])).
% 4.09/4.29  thf(commutativity_k9_subset_1, axiom,
% 4.09/4.29    (![A:$i,B:$i,C:$i]:
% 4.09/4.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.29       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 4.09/4.29  thf('52', plain,
% 4.09/4.29      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.09/4.29         (((k9_subset_1 @ X19 @ X21 @ X20) = (k9_subset_1 @ X19 @ X20 @ X21))
% 4.09/4.29          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 4.09/4.29      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 4.09/4.29  thf('53', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.09/4.29         ((k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X0)
% 4.09/4.29           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X2))),
% 4.09/4.29      inference('sup-', [status(thm)], ['51', '52'])).
% 4.09/4.29  thf('54', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['49', '50'])).
% 4.09/4.29  thf(redefinition_k9_subset_1, axiom,
% 4.09/4.29    (![A:$i,B:$i,C:$i]:
% 4.09/4.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.29       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 4.09/4.29  thf('55', plain,
% 4.09/4.29      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.09/4.29         (((k9_subset_1 @ X41 @ X39 @ X40) = (k3_xboole_0 @ X39 @ X40))
% 4.09/4.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 4.09/4.29      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 4.09/4.29  thf('56', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.09/4.29         ((k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X0)
% 4.09/4.29           = (k3_xboole_0 @ X2 @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['54', '55'])).
% 4.09/4.29  thf('57', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.09/4.29         ((k3_xboole_0 @ X2 @ X0)
% 4.09/4.29           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X2))),
% 4.09/4.29      inference('demod', [status(thm)], ['53', '56'])).
% 4.09/4.29  thf(commutativity_k2_xboole_0, axiom,
% 4.09/4.29    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.09/4.29  thf('58', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.09/4.29      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.09/4.29  thf('59', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['47', '48'])).
% 4.09/4.29  thf('60', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('61', plain,
% 4.09/4.29      (![X46 : $i, X47 : $i]:
% 4.09/4.29         ((r1_tarski @ X46 @ X47) | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47)))),
% 4.09/4.29      inference('cnf', [status(esa)], [t3_subset])).
% 4.09/4.29  thf('62', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 4.09/4.29      inference('sup-', [status(thm)], ['60', '61'])).
% 4.09/4.29  thf(t1_xboole_1, axiom,
% 4.09/4.29    (![A:$i,B:$i,C:$i]:
% 4.09/4.29     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 4.09/4.29       ( r1_tarski @ A @ C ) ))).
% 4.09/4.29  thf('63', plain,
% 4.09/4.29      (![X5 : $i, X6 : $i, X7 : $i]:
% 4.09/4.29         (~ (r1_tarski @ X5 @ X6)
% 4.09/4.29          | ~ (r1_tarski @ X6 @ X7)
% 4.09/4.29          | (r1_tarski @ X5 @ X7))),
% 4.09/4.29      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.09/4.29  thf('64', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['62', '63'])).
% 4.09/4.29  thf('65', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['59', '64'])).
% 4.09/4.29  thf('66', plain,
% 4.09/4.29      (![X46 : $i, X48 : $i]:
% 4.09/4.29         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 4.09/4.29      inference('cnf', [status(esa)], [t3_subset])).
% 4.09/4.29  thf('67', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         (m1_subset_1 @ sk_B @ 
% 4.09/4.29          (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))))),
% 4.09/4.29      inference('sup-', [status(thm)], ['65', '66'])).
% 4.09/4.29  thf('68', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         (m1_subset_1 @ sk_B @ 
% 4.09/4.29          (k1_zfmisc_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 4.09/4.29      inference('sup+', [status(thm)], ['58', '67'])).
% 4.09/4.29  thf('69', plain,
% 4.09/4.29      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.09/4.29         (((k9_subset_1 @ X41 @ X39 @ X40) = (k3_xboole_0 @ X39 @ X40))
% 4.09/4.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 4.09/4.29      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 4.09/4.29  thf('70', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         ((k9_subset_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ X1 @ sk_B)
% 4.09/4.29           = (k3_xboole_0 @ X1 @ sk_B))),
% 4.09/4.29      inference('sup-', [status(thm)], ['68', '69'])).
% 4.09/4.29  thf('71', plain,
% 4.09/4.29      (![X0 : $i]: ((k3_xboole_0 @ sk_B @ X0) = (k3_xboole_0 @ X0 @ sk_B))),
% 4.09/4.29      inference('sup+', [status(thm)], ['57', '70'])).
% 4.09/4.29  thf('72', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.09/4.29           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['18', '19'])).
% 4.09/4.29  thf('73', plain,
% 4.09/4.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 4.09/4.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('split', [status(esa)], ['43'])).
% 4.09/4.29  thf('74', plain,
% 4.09/4.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 4.09/4.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('sup+', [status(thm)], ['72', '73'])).
% 4.09/4.29  thf('75', plain,
% 4.09/4.29      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 4.09/4.29         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 4.09/4.29      inference('sup-', [status(thm)], ['6', '7'])).
% 4.09/4.29  thf('76', plain,
% 4.09/4.29      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 4.09/4.29          = (k2_tops_1 @ sk_A @ sk_B)))
% 4.09/4.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('sup+', [status(thm)], ['74', '75'])).
% 4.09/4.29  thf('77', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['4', '5'])).
% 4.09/4.29  thf('78', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['4', '5'])).
% 4.09/4.29  thf(t32_subset_1, axiom,
% 4.09/4.29    (![A:$i,B:$i]:
% 4.09/4.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.29       ( ![C:$i]:
% 4.09/4.29         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.29           ( ( k7_subset_1 @ A @ B @ C ) =
% 4.09/4.29             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 4.09/4.29  thf('79', plain,
% 4.09/4.29      (![X42 : $i, X43 : $i, X44 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 4.09/4.29          | ((k7_subset_1 @ X43 @ X44 @ X42)
% 4.09/4.29              = (k9_subset_1 @ X43 @ X44 @ (k3_subset_1 @ X43 @ X42)))
% 4.09/4.29          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43)))),
% 4.09/4.29      inference('cnf', [status(esa)], [t32_subset_1])).
% 4.09/4.29  thf('80', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))
% 4.09/4.29          | ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ sk_B)
% 4.09/4.29              = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ 
% 4.09/4.29                 (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('sup-', [status(thm)], ['78', '79'])).
% 4.09/4.29  thf('81', plain,
% 4.09/4.29      (((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ sk_B)
% 4.09/4.29         = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ 
% 4.09/4.29            (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['77', '80'])).
% 4.09/4.29  thf('82', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['4', '5'])).
% 4.09/4.29  thf('83', plain,
% 4.09/4.29      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 4.09/4.29          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 4.09/4.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.09/4.29  thf('84', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((k7_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ X0)
% 4.09/4.29           = (k4_xboole_0 @ sk_B @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['82', '83'])).
% 4.09/4.29  thf(dt_k2_subset_1, axiom,
% 4.09/4.29    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 4.09/4.29  thf('85', plain,
% 4.09/4.29      (![X25 : $i]: (m1_subset_1 @ (k2_subset_1 @ X25) @ (k1_zfmisc_1 @ X25))),
% 4.09/4.29      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 4.09/4.29  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 4.09/4.29  thf('86', plain, (![X22 : $i]: ((k2_subset_1 @ X22) = (X22))),
% 4.09/4.29      inference('cnf', [status(esa)], [d4_subset_1])).
% 4.09/4.29  thf('87', plain, (![X25 : $i]: (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X25))),
% 4.09/4.29      inference('demod', [status(thm)], ['85', '86'])).
% 4.09/4.29  thf('88', plain,
% 4.09/4.29      (![X23 : $i, X24 : $i]:
% 4.09/4.29         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 4.09/4.29          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 4.09/4.29      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.09/4.29  thf('89', plain,
% 4.09/4.29      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['87', '88'])).
% 4.09/4.29  thf(t4_subset_1, axiom,
% 4.09/4.29    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.09/4.29  thf('90', plain,
% 4.09/4.29      (![X45 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X45))),
% 4.09/4.29      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.09/4.29  thf(involutiveness_k3_subset_1, axiom,
% 4.09/4.29    (![A:$i,B:$i]:
% 4.09/4.29     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.09/4.29       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 4.09/4.29  thf('91', plain,
% 4.09/4.29      (![X34 : $i, X35 : $i]:
% 4.09/4.29         (((k3_subset_1 @ X35 @ (k3_subset_1 @ X35 @ X34)) = (X34))
% 4.09/4.29          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 4.09/4.29      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 4.09/4.29  thf('92', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['90', '91'])).
% 4.09/4.29  thf('93', plain,
% 4.09/4.29      (![X45 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X45))),
% 4.09/4.29      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.09/4.29  thf('94', plain,
% 4.09/4.29      (![X23 : $i, X24 : $i]:
% 4.09/4.29         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 4.09/4.29          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 4.09/4.29      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.09/4.29  thf('95', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['93', '94'])).
% 4.09/4.29  thf(t3_boole, axiom,
% 4.09/4.29    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.09/4.29  thf('96', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 4.09/4.29      inference('cnf', [status(esa)], [t3_boole])).
% 4.09/4.29  thf('97', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 4.09/4.29      inference('sup+', [status(thm)], ['95', '96'])).
% 4.09/4.29  thf('98', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 4.09/4.29      inference('demod', [status(thm)], ['92', '97'])).
% 4.09/4.29  thf('99', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['4', '5'])).
% 4.09/4.29  thf('100', plain,
% 4.09/4.29      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.09/4.29         (((k9_subset_1 @ X19 @ X21 @ X20) = (k9_subset_1 @ X19 @ X20 @ X21))
% 4.09/4.29          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 4.09/4.29      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 4.09/4.29  thf('101', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ sk_B)
% 4.09/4.29           = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['99', '100'])).
% 4.09/4.29  thf('102', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['4', '5'])).
% 4.09/4.29  thf('103', plain,
% 4.09/4.29      (![X39 : $i, X40 : $i, X41 : $i]:
% 4.09/4.29         (((k9_subset_1 @ X41 @ X39 @ X40) = (k3_xboole_0 @ X39 @ X40))
% 4.09/4.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 4.09/4.29      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 4.09/4.29  thf('104', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ X0 @ sk_B)
% 4.09/4.29           = (k3_xboole_0 @ X0 @ sk_B))),
% 4.09/4.29      inference('sup-', [status(thm)], ['102', '103'])).
% 4.09/4.29  thf('105', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((k3_xboole_0 @ X0 @ sk_B)
% 4.09/4.29           = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B @ X0))),
% 4.09/4.29      inference('demod', [status(thm)], ['101', '104'])).
% 4.09/4.29  thf('106', plain,
% 4.09/4.29      (((k1_xboole_0)
% 4.09/4.29         = (k3_xboole_0 @ (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) @ 
% 4.09/4.29            sk_B))),
% 4.09/4.29      inference('demod', [status(thm)], ['81', '84', '89', '98', '105'])).
% 4.09/4.29  thf('107', plain,
% 4.09/4.29      ((((k1_xboole_0) = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 4.09/4.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('sup+', [status(thm)], ['76', '106'])).
% 4.09/4.29  thf('108', plain,
% 4.09/4.29      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 4.09/4.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('sup+', [status(thm)], ['71', '107'])).
% 4.09/4.29  thf(t48_xboole_1, axiom,
% 4.09/4.29    (![A:$i,B:$i]:
% 4.09/4.29     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.09/4.29  thf('109', plain,
% 4.09/4.29      (![X17 : $i, X18 : $i]:
% 4.09/4.29         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 4.09/4.29           = (k3_xboole_0 @ X17 @ X18))),
% 4.09/4.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.09/4.29  thf('110', plain,
% 4.09/4.29      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 4.09/4.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.09/4.29  thf('111', plain,
% 4.09/4.29      (![X46 : $i, X48 : $i]:
% 4.09/4.29         ((m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X48)) | ~ (r1_tarski @ X46 @ X48))),
% 4.09/4.29      inference('cnf', [status(esa)], [t3_subset])).
% 4.09/4.29  thf('112', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['110', '111'])).
% 4.09/4.29  thf('113', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 4.09/4.29      inference('sup+', [status(thm)], ['109', '112'])).
% 4.09/4.29  thf('114', plain,
% 4.09/4.29      (![X23 : $i, X24 : $i]:
% 4.09/4.29         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 4.09/4.29          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 4.09/4.29      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.09/4.29  thf('115', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 4.09/4.29           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['113', '114'])).
% 4.09/4.29  thf('116', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['110', '111'])).
% 4.09/4.29  thf('117', plain,
% 4.09/4.29      (![X34 : $i, X35 : $i]:
% 4.09/4.29         (((k3_subset_1 @ X35 @ (k3_subset_1 @ X35 @ X34)) = (X34))
% 4.09/4.29          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 4.09/4.29      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 4.09/4.29  thf('118', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 4.09/4.29           = (k4_xboole_0 @ X0 @ X1))),
% 4.09/4.29      inference('sup-', [status(thm)], ['116', '117'])).
% 4.09/4.29  thf('119', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['110', '111'])).
% 4.09/4.29  thf('120', plain,
% 4.09/4.29      (![X23 : $i, X24 : $i]:
% 4.09/4.29         (((k3_subset_1 @ X23 @ X24) = (k4_xboole_0 @ X23 @ X24))
% 4.09/4.29          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 4.09/4.29      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.09/4.29  thf('121', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.09/4.29           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['119', '120'])).
% 4.09/4.29  thf('122', plain,
% 4.09/4.29      (![X17 : $i, X18 : $i]:
% 4.09/4.29         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 4.09/4.29           = (k3_xboole_0 @ X17 @ X18))),
% 4.09/4.29      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.09/4.29  thf('123', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 4.09/4.29           = (k3_xboole_0 @ X1 @ X0))),
% 4.09/4.29      inference('sup+', [status(thm)], ['121', '122'])).
% 4.09/4.29  thf('124', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 4.09/4.29           = (k4_xboole_0 @ X0 @ X1))),
% 4.09/4.29      inference('demod', [status(thm)], ['118', '123'])).
% 4.09/4.29  thf('125', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         ((k4_xboole_0 @ X0 @ X1)
% 4.09/4.29           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 4.09/4.29      inference('demod', [status(thm)], ['115', '124'])).
% 4.09/4.29  thf('126', plain, (![X25 : $i]: (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X25))),
% 4.09/4.29      inference('demod', [status(thm)], ['85', '86'])).
% 4.09/4.29  thf('127', plain,
% 4.09/4.29      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 4.09/4.29          | ((k7_subset_1 @ X37 @ X36 @ X38) = (k4_xboole_0 @ X36 @ X38)))),
% 4.09/4.29      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 4.09/4.29  thf('128', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 4.09/4.29      inference('sup-', [status(thm)], ['126', '127'])).
% 4.09/4.29  thf('129', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         ((k7_subset_1 @ X1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.09/4.29           = (k4_xboole_0 @ X1 @ X0))),
% 4.09/4.29      inference('sup+', [status(thm)], ['125', '128'])).
% 4.09/4.29  thf('130', plain,
% 4.09/4.29      ((((k7_subset_1 @ sk_B @ sk_B @ k1_xboole_0)
% 4.09/4.29          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 4.09/4.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('sup+', [status(thm)], ['108', '129'])).
% 4.09/4.29  thf('131', plain,
% 4.09/4.29      (![X0 : $i, X1 : $i]:
% 4.09/4.29         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 4.09/4.29      inference('sup-', [status(thm)], ['126', '127'])).
% 4.09/4.29  thf('132', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 4.09/4.29      inference('cnf', [status(esa)], [t3_boole])).
% 4.09/4.29  thf('133', plain,
% 4.09/4.29      (![X0 : $i]: ((k7_subset_1 @ X0 @ X0 @ k1_xboole_0) = (X0))),
% 4.09/4.29      inference('sup+', [status(thm)], ['131', '132'])).
% 4.09/4.29  thf('134', plain,
% 4.09/4.29      ((((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 4.09/4.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('demod', [status(thm)], ['130', '133'])).
% 4.09/4.29  thf('135', plain,
% 4.09/4.29      (((k1_tops_1 @ sk_A @ sk_B)
% 4.09/4.29         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 4.09/4.29      inference('demod', [status(thm)], ['26', '29'])).
% 4.09/4.29  thf('136', plain,
% 4.09/4.29      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 4.09/4.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('sup+', [status(thm)], ['134', '135'])).
% 4.09/4.29  thf('137', plain,
% 4.09/4.29      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf(fc9_tops_1, axiom,
% 4.09/4.29    (![A:$i,B:$i]:
% 4.09/4.29     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 4.09/4.29         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.09/4.29       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 4.09/4.29  thf('138', plain,
% 4.09/4.29      (![X56 : $i, X57 : $i]:
% 4.09/4.29         (~ (l1_pre_topc @ X56)
% 4.09/4.29          | ~ (v2_pre_topc @ X56)
% 4.09/4.29          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 4.09/4.29          | (v3_pre_topc @ (k1_tops_1 @ X56 @ X57) @ X56))),
% 4.09/4.29      inference('cnf', [status(esa)], [fc9_tops_1])).
% 4.09/4.29  thf('139', plain,
% 4.09/4.29      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 4.09/4.29        | ~ (v2_pre_topc @ sk_A)
% 4.09/4.29        | ~ (l1_pre_topc @ sk_A))),
% 4.09/4.29      inference('sup-', [status(thm)], ['137', '138'])).
% 4.09/4.29  thf('140', plain, ((v2_pre_topc @ sk_A)),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 4.09/4.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.29  thf('142', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 4.09/4.29      inference('demod', [status(thm)], ['139', '140', '141'])).
% 4.09/4.29  thf('143', plain,
% 4.09/4.29      (((v3_pre_topc @ sk_B @ sk_A))
% 4.09/4.29         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('sup+', [status(thm)], ['136', '142'])).
% 4.09/4.29  thf('144', plain,
% 4.09/4.29      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 4.09/4.29      inference('split', [status(esa)], ['45'])).
% 4.09/4.29  thf('145', plain,
% 4.09/4.29      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 4.09/4.29       ~
% 4.09/4.29       (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['143', '144'])).
% 4.09/4.29  thf('146', plain,
% 4.09/4.29      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 4.09/4.29       (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 4.09/4.29      inference('split', [status(esa)], ['43'])).
% 4.09/4.29  thf('147', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 4.09/4.29      inference('sat_resolution*', [status(thm)], ['46', '145', '146'])).
% 4.09/4.29  thf('148', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 4.09/4.29      inference('simpl_trail', [status(thm)], ['44', '147'])).
% 4.09/4.29  thf('149', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.09/4.29          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 4.09/4.29          | ~ (r1_tarski @ sk_B @ X0))),
% 4.09/4.29      inference('demod', [status(thm)], ['42', '148'])).
% 4.09/4.29  thf('150', plain,
% 4.09/4.29      ((~ (r1_tarski @ sk_B @ sk_B)
% 4.09/4.29        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 4.09/4.29      inference('sup-', [status(thm)], ['37', '149'])).
% 4.09/4.29  thf('151', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 4.09/4.29      inference('cnf', [status(esa)], [t3_boole])).
% 4.09/4.29  thf('152', plain,
% 4.09/4.29      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 4.09/4.29      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.09/4.29  thf('153', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 4.09/4.29      inference('sup+', [status(thm)], ['151', '152'])).
% 4.09/4.29  thf('154', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 4.09/4.29      inference('demod', [status(thm)], ['150', '153'])).
% 4.09/4.29  thf('155', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 4.09/4.29      inference('demod', [status(thm)], ['36', '154'])).
% 4.09/4.29  thf('156', plain,
% 4.09/4.29      (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 4.09/4.29      inference('demod', [status(thm)], ['21', '155'])).
% 4.09/4.29  thf('157', plain,
% 4.09/4.29      (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29         = (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 4.09/4.29      inference('sup+', [status(thm)], ['8', '156'])).
% 4.09/4.29  thf('158', plain,
% 4.09/4.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 4.09/4.29         <= (~
% 4.09/4.29             (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('split', [status(esa)], ['45'])).
% 4.09/4.29  thf('159', plain,
% 4.09/4.29      (![X0 : $i]:
% 4.09/4.29         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 4.09/4.29           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 4.09/4.29      inference('sup-', [status(thm)], ['18', '19'])).
% 4.09/4.29  thf('160', plain,
% 4.09/4.29      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 4.09/4.29         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 4.09/4.29      inference('sup-', [status(thm)], ['6', '7'])).
% 4.09/4.29  thf('161', plain,
% 4.09/4.29      ((((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29          != (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 4.09/4.29         <= (~
% 4.09/4.29             (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 4.09/4.29      inference('demod', [status(thm)], ['158', '159', '160'])).
% 4.09/4.29  thf('162', plain,
% 4.09/4.29      (~
% 4.09/4.29       (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 4.09/4.29             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 4.09/4.29      inference('sat_resolution*', [status(thm)], ['46', '145'])).
% 4.09/4.29  thf('163', plain,
% 4.09/4.29      (((k2_tops_1 @ sk_A @ sk_B)
% 4.09/4.29         != (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 4.09/4.29      inference('simpl_trail', [status(thm)], ['161', '162'])).
% 4.09/4.29  thf('164', plain, ($false),
% 4.09/4.29      inference('simplify_reflect-', [status(thm)], ['157', '163'])).
% 4.09/4.29  
% 4.09/4.29  % SZS output end Refutation
% 4.09/4.29  
% 4.09/4.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
