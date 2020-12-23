%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zxGAZUzTNr

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:23 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 223 expanded)
%              Number of leaves         :   43 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          : 1318 (2682 expanded)
%              Number of equality atoms :   81 ( 151 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k1_tops_1 @ X61 @ X60 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X61 ) @ X60 @ ( k2_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X42 @ X44 )
        = ( k4_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X26 @ X27 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('11',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( v3_pre_topc @ X53 @ X54 )
      | ~ ( r1_tarski @ X53 @ X55 )
      | ( r1_tarski @ X53 @ ( k1_tops_1 @ X54 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( ( k2_tops_1 @ X52 @ X51 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X52 ) @ ( k2_pre_topc @ X52 @ X51 ) @ ( k1_tops_1 @ X52 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X47 @ X48 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X38 @ X37 @ X39 ) @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k2_pre_topc @ X59 @ X58 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 @ ( k2_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X42 @ X44 )
        = ( k4_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('57',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ( X15
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X12 @ X11 ) @ X11 )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X12 @ X11 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('59',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('60',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('66',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('68',plain,(
    ! [X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(t111_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('69',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X22 @ X24 ) @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('70',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('71',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('72',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('73',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X22 @ X24 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X23 @ X24 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('77',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('78',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('80',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','81'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('83',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('84',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X45 @ X46 ) )
      = ( k3_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('85',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('88',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('90',plain,(
    ! [X25: $i] :
      ( ( k2_xboole_0 @ X25 @ k1_xboole_0 )
      = X25 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['86','91'])).

thf('93',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['56','92'])).

thf('94',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('97',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X49 @ X50 ) @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('98',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['95','101'])).

thf('103',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zxGAZUzTNr
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:45:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 1.92/2.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.92/2.09  % Solved by: fo/fo7.sh
% 1.92/2.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.92/2.09  % done 2474 iterations in 1.636s
% 1.92/2.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.92/2.09  % SZS output start Refutation
% 1.92/2.09  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.92/2.09  thf(sk_A_type, type, sk_A: $i).
% 1.92/2.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.92/2.09  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.92/2.09  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.92/2.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.92/2.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.92/2.09  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.92/2.09  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.92/2.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.92/2.09  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.92/2.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.92/2.09  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.92/2.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.92/2.09  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.92/2.09  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.92/2.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.92/2.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.92/2.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.92/2.09  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.92/2.09  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.92/2.09  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.92/2.09  thf(sk_B_type, type, sk_B: $i).
% 1.92/2.09  thf(t76_tops_1, conjecture,
% 1.92/2.09    (![A:$i]:
% 1.92/2.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.92/2.09       ( ![B:$i]:
% 1.92/2.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.92/2.09           ( ( v3_pre_topc @ B @ A ) <=>
% 1.92/2.09             ( ( k2_tops_1 @ A @ B ) =
% 1.92/2.09               ( k7_subset_1 @
% 1.92/2.09                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.92/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.92/2.09    (~( ![A:$i]:
% 1.92/2.09        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.92/2.09          ( ![B:$i]:
% 1.92/2.09            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.92/2.09              ( ( v3_pre_topc @ B @ A ) <=>
% 1.92/2.09                ( ( k2_tops_1 @ A @ B ) =
% 1.92/2.09                  ( k7_subset_1 @
% 1.92/2.09                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.92/2.09    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.92/2.09  thf('0', plain,
% 1.92/2.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.09              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.92/2.09        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf('1', plain,
% 1.92/2.09      (~
% 1.92/2.09       (((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.92/2.09       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.92/2.09      inference('split', [status(esa)], ['0'])).
% 1.92/2.09  thf('2', plain,
% 1.92/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf(t74_tops_1, axiom,
% 1.92/2.09    (![A:$i]:
% 1.92/2.09     ( ( l1_pre_topc @ A ) =>
% 1.92/2.09       ( ![B:$i]:
% 1.92/2.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.92/2.09           ( ( k1_tops_1 @ A @ B ) =
% 1.92/2.09             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.92/2.09  thf('3', plain,
% 1.92/2.09      (![X60 : $i, X61 : $i]:
% 1.92/2.09         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 1.92/2.09          | ((k1_tops_1 @ X61 @ X60)
% 1.92/2.09              = (k7_subset_1 @ (u1_struct_0 @ X61) @ X60 @ 
% 1.92/2.09                 (k2_tops_1 @ X61 @ X60)))
% 1.92/2.09          | ~ (l1_pre_topc @ X61))),
% 1.92/2.09      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.92/2.09  thf('4', plain,
% 1.92/2.09      ((~ (l1_pre_topc @ sk_A)
% 1.92/2.09        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.92/2.09            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.92/2.09               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.92/2.09      inference('sup-', [status(thm)], ['2', '3'])).
% 1.92/2.09  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf('6', plain,
% 1.92/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf(redefinition_k7_subset_1, axiom,
% 1.92/2.09    (![A:$i,B:$i,C:$i]:
% 1.92/2.09     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.92/2.09       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.92/2.09  thf('7', plain,
% 1.92/2.09      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.92/2.09         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 1.92/2.09          | ((k7_subset_1 @ X43 @ X42 @ X44) = (k4_xboole_0 @ X42 @ X44)))),
% 1.92/2.09      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.92/2.09  thf('8', plain,
% 1.92/2.09      (![X0 : $i]:
% 1.92/2.09         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.92/2.09           = (k4_xboole_0 @ sk_B @ X0))),
% 1.92/2.09      inference('sup-', [status(thm)], ['6', '7'])).
% 1.92/2.09  thf('9', plain,
% 1.92/2.09      (((k1_tops_1 @ sk_A @ sk_B)
% 1.92/2.09         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.92/2.09      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.92/2.09  thf(t36_xboole_1, axiom,
% 1.92/2.09    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.92/2.09  thf('10', plain,
% 1.92/2.09      (![X26 : $i, X27 : $i]: (r1_tarski @ (k4_xboole_0 @ X26 @ X27) @ X26)),
% 1.92/2.09      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.92/2.09  thf('11', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.92/2.09      inference('sup+', [status(thm)], ['9', '10'])).
% 1.92/2.09  thf('12', plain,
% 1.92/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf('13', plain,
% 1.92/2.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.92/2.09        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf('14', plain,
% 1.92/2.09      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.92/2.09      inference('split', [status(esa)], ['13'])).
% 1.92/2.09  thf('15', plain,
% 1.92/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf(t56_tops_1, axiom,
% 1.92/2.09    (![A:$i]:
% 1.92/2.09     ( ( l1_pre_topc @ A ) =>
% 1.92/2.09       ( ![B:$i]:
% 1.92/2.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.92/2.09           ( ![C:$i]:
% 1.92/2.09             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.92/2.09               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.92/2.09                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.92/2.09  thf('16', plain,
% 1.92/2.09      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.92/2.09         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.92/2.09          | ~ (v3_pre_topc @ X53 @ X54)
% 1.92/2.09          | ~ (r1_tarski @ X53 @ X55)
% 1.92/2.09          | (r1_tarski @ X53 @ (k1_tops_1 @ X54 @ X55))
% 1.92/2.09          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.92/2.09          | ~ (l1_pre_topc @ X54))),
% 1.92/2.09      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.92/2.09  thf('17', plain,
% 1.92/2.09      (![X0 : $i]:
% 1.92/2.09         (~ (l1_pre_topc @ sk_A)
% 1.92/2.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.92/2.09          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.92/2.09          | ~ (r1_tarski @ sk_B @ X0)
% 1.92/2.09          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.92/2.09      inference('sup-', [status(thm)], ['15', '16'])).
% 1.92/2.09  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf('19', plain,
% 1.92/2.09      (![X0 : $i]:
% 1.92/2.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.92/2.09          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.92/2.09          | ~ (r1_tarski @ sk_B @ X0)
% 1.92/2.09          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.92/2.09      inference('demod', [status(thm)], ['17', '18'])).
% 1.92/2.09  thf('20', plain,
% 1.92/2.09      ((![X0 : $i]:
% 1.92/2.09          (~ (r1_tarski @ sk_B @ X0)
% 1.92/2.09           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.92/2.09           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.92/2.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.92/2.09      inference('sup-', [status(thm)], ['14', '19'])).
% 1.92/2.09  thf('21', plain,
% 1.92/2.09      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.92/2.09         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.92/2.09      inference('sup-', [status(thm)], ['12', '20'])).
% 1.92/2.09  thf(d10_xboole_0, axiom,
% 1.92/2.09    (![A:$i,B:$i]:
% 1.92/2.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.92/2.09  thf('22', plain,
% 1.92/2.09      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 1.92/2.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.92/2.09  thf('23', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 1.92/2.09      inference('simplify', [status(thm)], ['22'])).
% 1.92/2.09  thf('24', plain,
% 1.92/2.09      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.92/2.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.92/2.09      inference('demod', [status(thm)], ['21', '23'])).
% 1.92/2.09  thf('25', plain,
% 1.92/2.09      (![X17 : $i, X19 : $i]:
% 1.92/2.09         (((X17) = (X19))
% 1.92/2.09          | ~ (r1_tarski @ X19 @ X17)
% 1.92/2.09          | ~ (r1_tarski @ X17 @ X19))),
% 1.92/2.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.92/2.09  thf('26', plain,
% 1.92/2.09      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 1.92/2.09         | ((k1_tops_1 @ sk_A @ sk_B) = (sk_B))))
% 1.92/2.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.92/2.09      inference('sup-', [status(thm)], ['24', '25'])).
% 1.92/2.09  thf('27', plain,
% 1.92/2.09      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.92/2.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.92/2.09      inference('sup-', [status(thm)], ['11', '26'])).
% 1.92/2.09  thf('28', plain,
% 1.92/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf(l78_tops_1, axiom,
% 1.92/2.09    (![A:$i]:
% 1.92/2.09     ( ( l1_pre_topc @ A ) =>
% 1.92/2.09       ( ![B:$i]:
% 1.92/2.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.92/2.09           ( ( k2_tops_1 @ A @ B ) =
% 1.92/2.09             ( k7_subset_1 @
% 1.92/2.09               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.92/2.09               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.92/2.09  thf('29', plain,
% 1.92/2.09      (![X51 : $i, X52 : $i]:
% 1.92/2.09         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 1.92/2.09          | ((k2_tops_1 @ X52 @ X51)
% 1.92/2.09              = (k7_subset_1 @ (u1_struct_0 @ X52) @ 
% 1.92/2.09                 (k2_pre_topc @ X52 @ X51) @ (k1_tops_1 @ X52 @ X51)))
% 1.92/2.09          | ~ (l1_pre_topc @ X52))),
% 1.92/2.09      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.92/2.09  thf('30', plain,
% 1.92/2.09      ((~ (l1_pre_topc @ sk_A)
% 1.92/2.09        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.09               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.92/2.09      inference('sup-', [status(thm)], ['28', '29'])).
% 1.92/2.09  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf('32', plain,
% 1.92/2.09      (((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.92/2.09            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.92/2.09      inference('demod', [status(thm)], ['30', '31'])).
% 1.92/2.09  thf('33', plain,
% 1.92/2.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.92/2.09         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.92/2.09      inference('sup+', [status(thm)], ['27', '32'])).
% 1.92/2.09  thf('34', plain,
% 1.92/2.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.09              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.92/2.09         <= (~
% 1.92/2.09             (((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.92/2.09      inference('split', [status(esa)], ['0'])).
% 1.92/2.09  thf('35', plain,
% 1.92/2.09      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 1.92/2.09         <= (~
% 1.92/2.09             (((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.09                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 1.92/2.09             ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.92/2.09      inference('sup-', [status(thm)], ['33', '34'])).
% 1.92/2.09  thf('36', plain,
% 1.92/2.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.92/2.09       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.92/2.09      inference('simplify', [status(thm)], ['35'])).
% 1.92/2.09  thf('37', plain,
% 1.92/2.09      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.09          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.09             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.92/2.09       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.92/2.09      inference('split', [status(esa)], ['13'])).
% 1.92/2.09  thf('38', plain,
% 1.92/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf(dt_k2_tops_1, axiom,
% 1.92/2.09    (![A:$i,B:$i]:
% 1.92/2.09     ( ( ( l1_pre_topc @ A ) & 
% 1.92/2.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.92/2.09       ( m1_subset_1 @
% 1.92/2.09         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.92/2.09  thf('39', plain,
% 1.92/2.09      (![X47 : $i, X48 : $i]:
% 1.92/2.09         (~ (l1_pre_topc @ X47)
% 1.92/2.09          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.92/2.09          | (m1_subset_1 @ (k2_tops_1 @ X47 @ X48) @ 
% 1.92/2.09             (k1_zfmisc_1 @ (u1_struct_0 @ X47))))),
% 1.92/2.09      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.92/2.09  thf('40', plain,
% 1.92/2.09      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.92/2.09         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.92/2.09        | ~ (l1_pre_topc @ sk_A))),
% 1.92/2.09      inference('sup-', [status(thm)], ['38', '39'])).
% 1.92/2.09  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf('42', plain,
% 1.92/2.09      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.92/2.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.09      inference('demod', [status(thm)], ['40', '41'])).
% 1.92/2.09  thf('43', plain,
% 1.92/2.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.09  thf(dt_k4_subset_1, axiom,
% 1.92/2.09    (![A:$i,B:$i,C:$i]:
% 1.92/2.09     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.92/2.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.92/2.09       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.92/2.09  thf('44', plain,
% 1.92/2.09      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.92/2.09         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 1.92/2.10          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 1.92/2.10          | (m1_subset_1 @ (k4_subset_1 @ X38 @ X37 @ X39) @ 
% 1.92/2.10             (k1_zfmisc_1 @ X38)))),
% 1.92/2.10      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 1.92/2.10  thf('45', plain,
% 1.92/2.10      (![X0 : $i]:
% 1.92/2.10         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.92/2.10           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.92/2.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.92/2.10      inference('sup-', [status(thm)], ['43', '44'])).
% 1.92/2.10  thf('46', plain,
% 1.92/2.10      ((m1_subset_1 @ 
% 1.92/2.10        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.92/2.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['42', '45'])).
% 1.92/2.10  thf('47', plain,
% 1.92/2.10      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.10  thf(t65_tops_1, axiom,
% 1.92/2.10    (![A:$i]:
% 1.92/2.10     ( ( l1_pre_topc @ A ) =>
% 1.92/2.10       ( ![B:$i]:
% 1.92/2.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.92/2.10           ( ( k2_pre_topc @ A @ B ) =
% 1.92/2.10             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.92/2.10  thf('48', plain,
% 1.92/2.10      (![X58 : $i, X59 : $i]:
% 1.92/2.10         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 1.92/2.10          | ((k2_pre_topc @ X59 @ X58)
% 1.92/2.10              = (k4_subset_1 @ (u1_struct_0 @ X59) @ X58 @ 
% 1.92/2.10                 (k2_tops_1 @ X59 @ X58)))
% 1.92/2.10          | ~ (l1_pre_topc @ X59))),
% 1.92/2.10      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.92/2.10  thf('49', plain,
% 1.92/2.10      ((~ (l1_pre_topc @ sk_A)
% 1.92/2.10        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.92/2.10            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.92/2.10               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.92/2.10      inference('sup-', [status(thm)], ['47', '48'])).
% 1.92/2.10  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.92/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.10  thf('51', plain,
% 1.92/2.10      (((k2_pre_topc @ sk_A @ sk_B)
% 1.92/2.10         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.92/2.10            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.92/2.10      inference('demod', [status(thm)], ['49', '50'])).
% 1.92/2.10  thf('52', plain,
% 1.92/2.10      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.92/2.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.10      inference('demod', [status(thm)], ['46', '51'])).
% 1.92/2.10  thf('53', plain,
% 1.92/2.10      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.92/2.10         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 1.92/2.10          | ((k7_subset_1 @ X43 @ X42 @ X44) = (k4_xboole_0 @ X42 @ X44)))),
% 1.92/2.10      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.92/2.10  thf('54', plain,
% 1.92/2.10      (![X0 : $i]:
% 1.92/2.10         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.92/2.10           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.92/2.10      inference('sup-', [status(thm)], ['52', '53'])).
% 1.92/2.10  thf('55', plain,
% 1.92/2.10      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.10          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.10             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.92/2.10         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.10                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.92/2.10      inference('split', [status(esa)], ['13'])).
% 1.92/2.10  thf('56', plain,
% 1.92/2.10      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.10          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.92/2.10         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.10                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.92/2.10      inference('sup+', [status(thm)], ['54', '55'])).
% 1.92/2.10  thf(d5_xboole_0, axiom,
% 1.92/2.10    (![A:$i,B:$i,C:$i]:
% 1.92/2.10     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.92/2.10       ( ![D:$i]:
% 1.92/2.10         ( ( r2_hidden @ D @ C ) <=>
% 1.92/2.10           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.92/2.10  thf('57', plain,
% 1.92/2.10      (![X11 : $i, X12 : $i, X15 : $i]:
% 1.92/2.10         (((X15) = (k4_xboole_0 @ X11 @ X12))
% 1.92/2.10          | (r2_hidden @ (sk_D_1 @ X15 @ X12 @ X11) @ X11)
% 1.92/2.10          | (r2_hidden @ (sk_D_1 @ X15 @ X12 @ X11) @ X15))),
% 1.92/2.10      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.92/2.10  thf(t4_boole, axiom,
% 1.92/2.10    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.92/2.10  thf('58', plain,
% 1.92/2.10      (![X28 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X28) = (k1_xboole_0))),
% 1.92/2.10      inference('cnf', [status(esa)], [t4_boole])).
% 1.92/2.10  thf('59', plain,
% 1.92/2.10      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X14 @ X13)
% 1.92/2.10          | ~ (r2_hidden @ X14 @ X12)
% 1.92/2.10          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 1.92/2.10      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.92/2.10  thf('60', plain,
% 1.92/2.10      (![X11 : $i, X12 : $i, X14 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X14 @ X12)
% 1.92/2.10          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 1.92/2.10      inference('simplify', [status(thm)], ['59'])).
% 1.92/2.10  thf('61', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 1.92/2.10      inference('sup-', [status(thm)], ['58', '60'])).
% 1.92/2.10  thf('62', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.92/2.10      inference('condensation', [status(thm)], ['61'])).
% 1.92/2.10  thf('63', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]:
% 1.92/2.10         ((r2_hidden @ (sk_D_1 @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.92/2.10          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.92/2.10      inference('sup-', [status(thm)], ['57', '62'])).
% 1.92/2.10  thf('64', plain,
% 1.92/2.10      (![X28 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X28) = (k1_xboole_0))),
% 1.92/2.10      inference('cnf', [status(esa)], [t4_boole])).
% 1.92/2.10  thf('65', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]:
% 1.92/2.10         ((r2_hidden @ (sk_D_1 @ X1 @ X0 @ k1_xboole_0) @ X1)
% 1.92/2.10          | ((X1) = (k1_xboole_0)))),
% 1.92/2.10      inference('demod', [status(thm)], ['63', '64'])).
% 1.92/2.10  thf(idempotence_k3_xboole_0, axiom,
% 1.92/2.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.92/2.10  thf('66', plain, (![X16 : $i]: ((k3_xboole_0 @ X16 @ X16) = (X16))),
% 1.92/2.10      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.92/2.10  thf(t12_setfam_1, axiom,
% 1.92/2.10    (![A:$i,B:$i]:
% 1.92/2.10     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.92/2.10  thf('67', plain,
% 1.92/2.10      (![X45 : $i, X46 : $i]:
% 1.92/2.10         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 1.92/2.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.92/2.10  thf('68', plain,
% 1.92/2.10      (![X16 : $i]: ((k1_setfam_1 @ (k2_tarski @ X16 @ X16)) = (X16))),
% 1.92/2.10      inference('demod', [status(thm)], ['66', '67'])).
% 1.92/2.10  thf(t111_xboole_1, axiom,
% 1.92/2.10    (![A:$i,B:$i,C:$i]:
% 1.92/2.10     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.92/2.10       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 1.92/2.10  thf('69', plain,
% 1.92/2.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.92/2.10         ((k4_xboole_0 @ (k3_xboole_0 @ X22 @ X24) @ (k3_xboole_0 @ X23 @ X24))
% 1.92/2.10           = (k3_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X24))),
% 1.92/2.10      inference('cnf', [status(esa)], [t111_xboole_1])).
% 1.92/2.10  thf('70', plain,
% 1.92/2.10      (![X45 : $i, X46 : $i]:
% 1.92/2.10         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 1.92/2.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.92/2.10  thf('71', plain,
% 1.92/2.10      (![X45 : $i, X46 : $i]:
% 1.92/2.10         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 1.92/2.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.92/2.10  thf('72', plain,
% 1.92/2.10      (![X45 : $i, X46 : $i]:
% 1.92/2.10         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 1.92/2.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.92/2.10  thf('73', plain,
% 1.92/2.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.92/2.10         ((k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X22 @ X24)) @ 
% 1.92/2.10           (k1_setfam_1 @ (k2_tarski @ X23 @ X24)))
% 1.92/2.10           = (k1_setfam_1 @ (k2_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)))),
% 1.92/2.10      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 1.92/2.10  thf('74', plain,
% 1.92/2.10      (![X11 : $i, X12 : $i, X14 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X14 @ X12)
% 1.92/2.10          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 1.92/2.10      inference('simplify', [status(thm)], ['59'])).
% 1.92/2.10  thf('75', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X3 @ 
% 1.92/2.10             (k1_setfam_1 @ (k2_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0)))
% 1.92/2.10          | ~ (r2_hidden @ X3 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.92/2.10      inference('sup-', [status(thm)], ['73', '74'])).
% 1.92/2.10  thf('76', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.92/2.10          | ~ (r2_hidden @ X2 @ 
% 1.92/2.10               (k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))))),
% 1.92/2.10      inference('sup-', [status(thm)], ['68', '75'])).
% 1.92/2.10  thf(d4_xboole_0, axiom,
% 1.92/2.10    (![A:$i,B:$i,C:$i]:
% 1.92/2.10     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.92/2.10       ( ![D:$i]:
% 1.92/2.10         ( ( r2_hidden @ D @ C ) <=>
% 1.92/2.10           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.92/2.10  thf('77', plain,
% 1.92/2.10      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.92/2.10         (~ (r2_hidden @ X8 @ X7)
% 1.92/2.10          | (r2_hidden @ X8 @ X6)
% 1.92/2.10          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 1.92/2.10      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.92/2.10  thf('78', plain,
% 1.92/2.10      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.92/2.10         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.92/2.10      inference('simplify', [status(thm)], ['77'])).
% 1.92/2.10  thf('79', plain,
% 1.92/2.10      (![X45 : $i, X46 : $i]:
% 1.92/2.10         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 1.92/2.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.92/2.10  thf('80', plain,
% 1.92/2.10      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.92/2.10         ((r2_hidden @ X8 @ X6)
% 1.92/2.10          | ~ (r2_hidden @ X8 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 1.92/2.10      inference('demod', [status(thm)], ['78', '79'])).
% 1.92/2.10  thf('81', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.10         ~ (r2_hidden @ X2 @ 
% 1.92/2.10            (k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.92/2.10      inference('clc', [status(thm)], ['76', '80'])).
% 1.92/2.10  thf('82', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]:
% 1.92/2.10         ((k1_setfam_1 @ (k2_tarski @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 1.92/2.10           = (k1_xboole_0))),
% 1.92/2.10      inference('sup-', [status(thm)], ['65', '81'])).
% 1.92/2.10  thf(t100_xboole_1, axiom,
% 1.92/2.10    (![A:$i,B:$i]:
% 1.92/2.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.92/2.10  thf('83', plain,
% 1.92/2.10      (![X20 : $i, X21 : $i]:
% 1.92/2.10         ((k4_xboole_0 @ X20 @ X21)
% 1.92/2.10           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 1.92/2.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.92/2.10  thf('84', plain,
% 1.92/2.10      (![X45 : $i, X46 : $i]:
% 1.92/2.10         ((k1_setfam_1 @ (k2_tarski @ X45 @ X46)) = (k3_xboole_0 @ X45 @ X46))),
% 1.92/2.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.92/2.10  thf('85', plain,
% 1.92/2.10      (![X20 : $i, X21 : $i]:
% 1.92/2.10         ((k4_xboole_0 @ X20 @ X21)
% 1.92/2.10           = (k5_xboole_0 @ X20 @ (k1_setfam_1 @ (k2_tarski @ X20 @ X21))))),
% 1.92/2.10      inference('demod', [status(thm)], ['83', '84'])).
% 1.92/2.10  thf('86', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]:
% 1.92/2.10         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.92/2.10           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.92/2.10      inference('sup+', [status(thm)], ['82', '85'])).
% 1.92/2.10  thf('87', plain,
% 1.92/2.10      (![X28 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X28) = (k1_xboole_0))),
% 1.92/2.10      inference('cnf', [status(esa)], [t4_boole])).
% 1.92/2.10  thf(t98_xboole_1, axiom,
% 1.92/2.10    (![A:$i,B:$i]:
% 1.92/2.10     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.92/2.10  thf('88', plain,
% 1.92/2.10      (![X29 : $i, X30 : $i]:
% 1.92/2.10         ((k2_xboole_0 @ X29 @ X30)
% 1.92/2.10           = (k5_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29)))),
% 1.92/2.10      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.92/2.10  thf('89', plain,
% 1.92/2.10      (![X0 : $i]:
% 1.92/2.10         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.92/2.10      inference('sup+', [status(thm)], ['87', '88'])).
% 1.92/2.10  thf(t1_boole, axiom,
% 1.92/2.10    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.92/2.10  thf('90', plain, (![X25 : $i]: ((k2_xboole_0 @ X25 @ k1_xboole_0) = (X25))),
% 1.92/2.10      inference('cnf', [status(esa)], [t1_boole])).
% 1.92/2.10  thf('91', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.92/2.10      inference('sup+', [status(thm)], ['89', '90'])).
% 1.92/2.10  thf('92', plain,
% 1.92/2.10      (![X0 : $i, X1 : $i]:
% 1.92/2.10         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.92/2.10      inference('demod', [status(thm)], ['86', '91'])).
% 1.92/2.10  thf('93', plain,
% 1.92/2.10      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.92/2.10         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.10                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.92/2.10      inference('sup+', [status(thm)], ['56', '92'])).
% 1.92/2.10  thf('94', plain,
% 1.92/2.10      (((k1_tops_1 @ sk_A @ sk_B)
% 1.92/2.10         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.92/2.10      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.92/2.10  thf('95', plain,
% 1.92/2.10      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.92/2.10         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.10                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.92/2.10      inference('sup+', [status(thm)], ['93', '94'])).
% 1.92/2.10  thf('96', plain,
% 1.92/2.10      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.92/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.10  thf(fc9_tops_1, axiom,
% 1.92/2.10    (![A:$i,B:$i]:
% 1.92/2.10     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.92/2.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.92/2.10       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.92/2.10  thf('97', plain,
% 1.92/2.10      (![X49 : $i, X50 : $i]:
% 1.92/2.10         (~ (l1_pre_topc @ X49)
% 1.92/2.10          | ~ (v2_pre_topc @ X49)
% 1.92/2.10          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 1.92/2.10          | (v3_pre_topc @ (k1_tops_1 @ X49 @ X50) @ X49))),
% 1.92/2.10      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.92/2.10  thf('98', plain,
% 1.92/2.10      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.92/2.10        | ~ (v2_pre_topc @ sk_A)
% 1.92/2.10        | ~ (l1_pre_topc @ sk_A))),
% 1.92/2.10      inference('sup-', [status(thm)], ['96', '97'])).
% 1.92/2.10  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 1.92/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.10  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 1.92/2.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.10  thf('101', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.92/2.10      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.92/2.10  thf('102', plain,
% 1.92/2.10      (((v3_pre_topc @ sk_B @ sk_A))
% 1.92/2.10         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.10                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.92/2.10      inference('sup+', [status(thm)], ['95', '101'])).
% 1.92/2.10  thf('103', plain,
% 1.92/2.10      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.92/2.10      inference('split', [status(esa)], ['0'])).
% 1.92/2.10  thf('104', plain,
% 1.92/2.10      (~
% 1.92/2.10       (((k2_tops_1 @ sk_A @ sk_B)
% 1.92/2.10          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.92/2.10             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.92/2.10       ((v3_pre_topc @ sk_B @ sk_A))),
% 1.92/2.10      inference('sup-', [status(thm)], ['102', '103'])).
% 1.92/2.10  thf('105', plain, ($false),
% 1.92/2.10      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '104'])).
% 1.92/2.10  
% 1.92/2.10  % SZS output end Refutation
% 1.92/2.10  
% 1.92/2.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
