%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ybScUuNbaG

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:33 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 386 expanded)
%              Number of leaves         :   31 ( 123 expanded)
%              Depth                    :   13
%              Number of atoms          : 1400 (5043 expanded)
%              Number of equality atoms :   82 ( 242 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('6',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_pre_topc @ X36 @ X37 )
      | ~ ( r1_tarski @ X36 @ X38 )
      | ( r1_tarski @ X36 @ ( k1_tops_1 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B_1 @ X0 )
        | ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r1_tarski @ sk_B_1 @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 @ ( k2_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k2_tops_1 @ X35 @ X34 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k2_pre_topc @ X35 @ X34 ) @ ( k1_tops_1 @ X35 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X28 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('50',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('53',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X22 @ X20 )
        = ( k9_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('68',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('70',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X13 @ X12 @ X12 )
        = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['51','72'])).

thf('74',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('76',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r1_tarski @ X30 @ ( k2_pre_topc @ X31 @ X30 ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('82',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('83',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('86',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('88',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['83','86','87'])).

thf('89',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['74','88'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('91',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('92',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['74','88'])).

thf('93',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['73','89','90','91','92'])).

thf('94',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('97',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X32 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('98',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
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
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['95','101'])).

thf('103',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','47','48','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ybScUuNbaG
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:28:33 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 969 iterations in 0.517s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.77/0.96  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.77/0.96  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.77/0.96  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.77/0.96  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.77/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.77/0.96  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.77/0.96  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.77/0.96  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.77/0.96  thf(t76_tops_1, conjecture,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( ( v3_pre_topc @ B @ A ) <=>
% 0.77/0.96             ( ( k2_tops_1 @ A @ B ) =
% 0.77/0.96               ( k7_subset_1 @
% 0.77/0.96                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i]:
% 0.77/0.96        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.96          ( ![B:$i]:
% 0.77/0.96            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96              ( ( v3_pre_topc @ B @ A ) <=>
% 0.77/0.96                ( ( k2_tops_1 @ A @ B ) =
% 0.77/0.96                  ( k7_subset_1 @
% 0.77/0.96                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.77/0.96  thf('0', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 0.77/0.96        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      (~
% 0.77/0.96       (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.77/0.96       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('2', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('3', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 0.77/0.96        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('4', plain,
% 0.77/0.96      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('split', [status(esa)], ['3'])).
% 0.77/0.96  thf('5', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t56_tops_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.77/0.96                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf('6', plain,
% 0.77/0.96      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.77/0.96          | ~ (v3_pre_topc @ X36 @ X37)
% 0.77/0.96          | ~ (r1_tarski @ X36 @ X38)
% 0.77/0.96          | (r1_tarski @ X36 @ (k1_tops_1 @ X37 @ X38))
% 0.77/0.96          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.77/0.96          | ~ (l1_pre_topc @ X37))),
% 0.77/0.96      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.77/0.96  thf('7', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ sk_A)
% 0.77/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.77/0.96          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.77/0.96          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['5', '6'])).
% 0.77/0.96  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('9', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.77/0.96          | ~ (r1_tarski @ sk_B_1 @ X0)
% 0.77/0.96          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf('10', plain,
% 0.77/0.96      ((![X0 : $i]:
% 0.77/0.96          (~ (r1_tarski @ sk_B_1 @ X0)
% 0.77/0.96           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.77/0.96           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.77/0.96         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['4', '9'])).
% 0.77/0.96  thf('11', plain,
% 0.77/0.96      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.77/0.96         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 0.77/0.96         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['2', '10'])).
% 0.77/0.96  thf(d10_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.96  thf('12', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.96  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.77/0.96      inference('simplify', [status(thm)], ['12'])).
% 0.77/0.96  thf('14', plain,
% 0.77/0.96      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 0.77/0.96         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['11', '13'])).
% 0.77/0.96  thf('15', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t74_tops_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( ( k1_tops_1 @ A @ B ) =
% 0.77/0.96             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.77/0.96  thf('16', plain,
% 0.77/0.96      (![X39 : $i, X40 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.77/0.96          | ((k1_tops_1 @ X40 @ X39)
% 0.77/0.96              = (k7_subset_1 @ (u1_struct_0 @ X40) @ X39 @ 
% 0.77/0.96                 (k2_tops_1 @ X40 @ X39)))
% 0.77/0.96          | ~ (l1_pre_topc @ X40))),
% 0.77/0.96      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.77/0.96  thf('17', plain,
% 0.77/0.96      ((~ (l1_pre_topc @ sk_A)
% 0.77/0.96        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.77/0.96               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['15', '16'])).
% 0.77/0.96  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('19', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(redefinition_k7_subset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.77/0.96  thf('20', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.77/0.96          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.77/0.96      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.77/0.96  thf('21', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 0.77/0.96           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['19', '20'])).
% 0.77/0.96  thf('22', plain,
% 0.77/0.96      (((k1_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('demod', [status(thm)], ['17', '18', '21'])).
% 0.77/0.96  thf(t36_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.77/0.96  thf('23', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.77/0.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.77/0.96  thf('24', plain,
% 0.77/0.96      (![X0 : $i, X2 : $i]:
% 0.77/0.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.96  thf('25', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.77/0.96          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['23', '24'])).
% 0.77/0.96  thf('26', plain,
% 0.77/0.96      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.77/0.96        | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['22', '25'])).
% 0.77/0.96  thf('27', plain,
% 0.77/0.96      (((k1_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('demod', [status(thm)], ['17', '18', '21'])).
% 0.77/0.96  thf('28', plain,
% 0.77/0.96      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.77/0.96        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('demod', [status(thm)], ['26', '27'])).
% 0.77/0.96  thf('29', plain,
% 0.77/0.96      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 0.77/0.96         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['14', '28'])).
% 0.77/0.96  thf('30', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(l78_tops_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( ( k2_tops_1 @ A @ B ) =
% 0.77/0.96             ( k7_subset_1 @
% 0.77/0.96               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.77/0.96               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.77/0.96  thf('31', plain,
% 0.77/0.96      (![X34 : $i, X35 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.77/0.96          | ((k2_tops_1 @ X35 @ X34)
% 0.77/0.96              = (k7_subset_1 @ (u1_struct_0 @ X35) @ 
% 0.77/0.96                 (k2_pre_topc @ X35 @ X34) @ (k1_tops_1 @ X35 @ X34)))
% 0.77/0.96          | ~ (l1_pre_topc @ X35))),
% 0.77/0.96      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.77/0.96  thf('32', plain,
% 0.77/0.96      ((~ (l1_pre_topc @ sk_A)
% 0.77/0.96        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['30', '31'])).
% 0.77/0.96  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('34', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(dt_k2_pre_topc, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( l1_pre_topc @ A ) & 
% 0.77/0.96         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.77/0.96       ( m1_subset_1 @
% 0.77/0.96         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.77/0.96  thf('35', plain,
% 0.77/0.96      (![X28 : $i, X29 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ X28)
% 0.77/0.96          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.77/0.96          | (m1_subset_1 @ (k2_pre_topc @ X28 @ X29) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.77/0.96  thf('36', plain,
% 0.77/0.96      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.77/0.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96        | ~ (l1_pre_topc @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['34', '35'])).
% 0.77/0.96  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('38', plain,
% 0.77/0.96      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['36', '37'])).
% 0.77/0.96  thf('39', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.77/0.96          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.77/0.96      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.77/0.96  thf('40', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.77/0.96           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['38', '39'])).
% 0.77/0.96  thf('41', plain,
% 0.77/0.96      (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.77/0.96            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('demod', [status(thm)], ['32', '33', '40'])).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.77/0.96         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['29', '41'])).
% 0.77/0.96  thf('43', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.77/0.96           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['38', '39'])).
% 0.77/0.96  thf('44', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.77/0.96         <= (~
% 0.77/0.96             (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('45', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.77/0.96         <= (~
% 0.77/0.96             (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['43', '44'])).
% 0.77/0.96  thf('46', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 0.77/0.96         <= (~
% 0.77/0.96             (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 0.77/0.96             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['42', '45'])).
% 0.77/0.96  thf('47', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.77/0.96       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('simplify', [status(thm)], ['46'])).
% 0.77/0.96  thf('48', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.77/0.96       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('split', [status(esa)], ['3'])).
% 0.77/0.96  thf('49', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.77/0.96           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['38', '39'])).
% 0.77/0.96  thf('50', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('split', [status(esa)], ['3'])).
% 0.77/0.96  thf('51', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['49', '50'])).
% 0.77/0.96  thf('52', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.77/0.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.77/0.96  thf(t3_subset, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/0.96  thf('53', plain,
% 0.77/0.96      (![X25 : $i, X27 : $i]:
% 0.77/0.96         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.96  thf('54', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['52', '53'])).
% 0.77/0.96  thf('55', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['52', '53'])).
% 0.77/0.96  thf(t32_subset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96       ( ![C:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.77/0.96             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.77/0.96  thf('56', plain,
% 0.77/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.77/0.96          | ((k7_subset_1 @ X21 @ X22 @ X20)
% 0.77/0.96              = (k9_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X20)))
% 0.77/0.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.77/0.96  thf('57', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.77/0.96          | ((k7_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.77/0.96              = (k9_subset_1 @ X0 @ X2 @ 
% 0.77/0.96                 (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['55', '56'])).
% 0.77/0.96  thf('58', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['52', '53'])).
% 0.77/0.96  thf(d5_subset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.77/0.96  thf('59', plain,
% 0.77/0.96      (![X7 : $i, X8 : $i]:
% 0.77/0.96         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.77/0.96          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.77/0.96  thf('60', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.77/0.96           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['58', '59'])).
% 0.77/0.96  thf('61', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.77/0.96          | ((k7_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.77/0.96              = (k9_subset_1 @ X0 @ X2 @ 
% 0.77/0.96                 (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))))),
% 0.77/0.96      inference('demod', [status(thm)], ['57', '60'])).
% 0.77/0.96  thf('62', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2))
% 0.77/0.96           = (k9_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.77/0.96              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['54', '61'])).
% 0.77/0.96  thf('63', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['52', '53'])).
% 0.77/0.96  thf('64', plain,
% 0.77/0.96      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.77/0.96          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.77/0.96      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.77/0.96  thf('65', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 0.77/0.96           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 0.77/0.96      inference('sup-', [status(thm)], ['63', '64'])).
% 0.77/0.96  thf('66', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2))
% 0.77/0.96           = (k9_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.77/0.96              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2))))),
% 0.77/0.96      inference('demod', [status(thm)], ['62', '65'])).
% 0.77/0.96  thf('67', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.77/0.96      inference('simplify', [status(thm)], ['12'])).
% 0.77/0.96  thf('68', plain,
% 0.77/0.96      (![X25 : $i, X27 : $i]:
% 0.77/0.96         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.96  thf('69', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['67', '68'])).
% 0.77/0.96  thf(idempotence_k9_subset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.77/0.96  thf('70', plain,
% 0.77/0.96      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.77/0.96         (((k9_subset_1 @ X13 @ X12 @ X12) = (X12))
% 0.77/0.96          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.77/0.96      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.77/0.96  thf('71', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['69', '70'])).
% 0.77/0.96  thf('72', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.77/0.96           (k4_xboole_0 @ X1 @ X0))
% 0.77/0.96           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['66', '71'])).
% 0.77/0.96  thf('73', plain,
% 0.77/0.96      ((((k4_xboole_0 @ 
% 0.77/0.96          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.77/0.96           (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 0.77/0.96          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 0.77/0.96          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.77/0.96             (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['51', '72'])).
% 0.77/0.96  thf('74', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['49', '50'])).
% 0.77/0.96  thf('75', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t48_pre_topc, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.77/0.96  thf('76', plain,
% 0.77/0.96      (![X30 : $i, X31 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.77/0.96          | (r1_tarski @ X30 @ (k2_pre_topc @ X31 @ X30))
% 0.77/0.96          | ~ (l1_pre_topc @ X31))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.77/0.96  thf('77', plain,
% 0.77/0.96      ((~ (l1_pre_topc @ sk_A)
% 0.77/0.96        | (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['75', '76'])).
% 0.77/0.96  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('79', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 0.77/0.96      inference('demod', [status(thm)], ['77', '78'])).
% 0.77/0.96  thf('80', plain,
% 0.77/0.96      (![X25 : $i, X27 : $i]:
% 0.77/0.96         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.96  thf('81', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['79', '80'])).
% 0.77/0.96  thf(involutiveness_k3_subset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.77/0.96  thf('82', plain,
% 0.77/0.96      (![X15 : $i, X16 : $i]:
% 0.77/0.96         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 0.77/0.96          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.77/0.96      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.77/0.96  thf('83', plain,
% 0.77/0.96      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.77/0.96         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['81', '82'])).
% 0.77/0.96  thf('84', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['79', '80'])).
% 0.77/0.96  thf('85', plain,
% 0.77/0.96      (![X7 : $i, X8 : $i]:
% 0.77/0.96         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.77/0.96          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.77/0.96  thf('86', plain,
% 0.77/0.96      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 0.77/0.96         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['84', '85'])).
% 0.77/0.96  thf('87', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.77/0.96           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['58', '59'])).
% 0.77/0.96  thf('88', plain,
% 0.77/0.96      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.77/0.96         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 0.77/0.96      inference('demod', [status(thm)], ['83', '86', '87'])).
% 0.77/0.96  thf('89', plain,
% 0.77/0.96      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.77/0.96          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['74', '88'])).
% 0.77/0.96  thf('90', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['49', '50'])).
% 0.77/0.96  thf('91', plain,
% 0.77/0.96      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['49', '50'])).
% 0.77/0.96  thf('92', plain,
% 0.77/0.96      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.77/0.96          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['74', '88'])).
% 0.77/0.96  thf('93', plain,
% 0.77/0.96      ((((k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('demod', [status(thm)], ['73', '89', '90', '91', '92'])).
% 0.77/0.96  thf('94', plain,
% 0.77/0.96      (((k1_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('demod', [status(thm)], ['17', '18', '21'])).
% 0.77/0.96  thf('95', plain,
% 0.77/0.96      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['93', '94'])).
% 0.77/0.96  thf('96', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(fc9_tops_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.77/0.96         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.77/0.96       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.77/0.96  thf('97', plain,
% 0.77/0.96      (![X32 : $i, X33 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ X32)
% 0.77/0.96          | ~ (v2_pre_topc @ X32)
% 0.77/0.96          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.77/0.96          | (v3_pre_topc @ (k1_tops_1 @ X32 @ X33) @ X32))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.77/0.96  thf('98', plain,
% 0.77/0.96      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.77/0.96        | ~ (v2_pre_topc @ sk_A)
% 0.77/0.96        | ~ (l1_pre_topc @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['96', '97'])).
% 0.77/0.96  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('101', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.77/0.96      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.77/0.96  thf('102', plain,
% 0.77/0.96      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 0.77/0.96         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['95', '101'])).
% 0.77/0.96  thf('103', plain,
% 0.77/0.96      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('104', plain,
% 0.77/0.96      (~
% 0.77/0.96       (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.77/0.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 0.77/0.96       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['102', '103'])).
% 0.77/0.96  thf('105', plain, ($false),
% 0.77/0.96      inference('sat_resolution*', [status(thm)], ['1', '47', '48', '104'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
