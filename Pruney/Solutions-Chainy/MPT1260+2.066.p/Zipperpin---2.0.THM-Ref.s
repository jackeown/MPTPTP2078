%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qmsGwqGCIH

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:33 EST 2020

% Result     : Theorem 8.34s
% Output     : Refutation 8.34s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 339 expanded)
%              Number of leaves         :   39 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          : 1444 (4369 expanded)
%              Number of equality atoms :   79 ( 217 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

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
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v3_pre_topc @ X50 @ X51 )
      | ~ ( r1_tarski @ X50 @ X52 )
      | ( r1_tarski @ X50 @ ( k1_tops_1 @ X51 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
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

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('16',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X49 @ X48 ) @ X48 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k2_tops_1 @ X47 @ X46 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X47 ) @ ( k2_pre_topc @ X47 @ X46 ) @ ( k1_tops_1 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('35',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( l1_pre_topc @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X42 @ X43 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) ) ) ),
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

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X20 @ X19 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k4_subset_1 @ X29 @ X28 @ X30 )
        = ( k2_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k2_pre_topc @ X54 @ X53 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X54 ) @ X53 @ ( k2_tops_1 @ X54 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k3_subset_1 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['51','59'])).

thf('61',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('62',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('64',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('67',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('72',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('74',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k7_subset_1 @ X35 @ X36 @ X34 )
        = ( k9_subset_1 @ X35 @ X36 @ ( k3_subset_1 @ X35 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('77',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('82',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ X2 )
      = ( k4_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('85',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('87',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k9_subset_1 @ X24 @ X23 @ X23 )
        = X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['80','83','88'])).

thf('90',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['69','89'])).

thf('91',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['68','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('93',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k1_tops_1 @ X56 @ X55 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X31 @ X33 )
        = ( k4_xboole_0 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('100',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['91','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('102',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X44 @ X45 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('103',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['100','106'])).

thf('108',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','31','32','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qmsGwqGCIH
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:59:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 8.34/8.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.34/8.51  % Solved by: fo/fo7.sh
% 8.34/8.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.34/8.51  % done 11975 iterations in 8.060s
% 8.34/8.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.34/8.51  % SZS output start Refutation
% 8.34/8.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.34/8.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.34/8.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.34/8.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.34/8.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 8.34/8.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.34/8.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.34/8.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.34/8.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.34/8.51  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.34/8.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.34/8.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 8.34/8.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.34/8.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 8.34/8.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.34/8.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 8.34/8.51  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.34/8.51  thf(sk_A_type, type, sk_A: $i).
% 8.34/8.51  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 8.34/8.51  thf(t76_tops_1, conjecture,
% 8.34/8.51    (![A:$i]:
% 8.34/8.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.34/8.51       ( ![B:$i]:
% 8.34/8.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.34/8.51           ( ( v3_pre_topc @ B @ A ) <=>
% 8.34/8.51             ( ( k2_tops_1 @ A @ B ) =
% 8.34/8.51               ( k7_subset_1 @
% 8.34/8.51                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 8.34/8.51  thf(zf_stmt_0, negated_conjecture,
% 8.34/8.51    (~( ![A:$i]:
% 8.34/8.51        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.34/8.51          ( ![B:$i]:
% 8.34/8.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.34/8.51              ( ( v3_pre_topc @ B @ A ) <=>
% 8.34/8.51                ( ( k2_tops_1 @ A @ B ) =
% 8.34/8.51                  ( k7_subset_1 @
% 8.34/8.51                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 8.34/8.51    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 8.34/8.51  thf('0', plain,
% 8.34/8.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 8.34/8.51        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('1', plain,
% 8.34/8.51      (~
% 8.34/8.51       (((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 8.34/8.51       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 8.34/8.51      inference('split', [status(esa)], ['0'])).
% 8.34/8.51  thf('2', plain,
% 8.34/8.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('3', plain,
% 8.34/8.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 8.34/8.51        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('4', plain,
% 8.34/8.51      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 8.34/8.51      inference('split', [status(esa)], ['3'])).
% 8.34/8.51  thf('5', plain,
% 8.34/8.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf(t56_tops_1, axiom,
% 8.34/8.51    (![A:$i]:
% 8.34/8.51     ( ( l1_pre_topc @ A ) =>
% 8.34/8.51       ( ![B:$i]:
% 8.34/8.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.34/8.51           ( ![C:$i]:
% 8.34/8.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.34/8.51               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 8.34/8.51                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.34/8.51  thf('6', plain,
% 8.34/8.51      (![X50 : $i, X51 : $i, X52 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 8.34/8.51          | ~ (v3_pre_topc @ X50 @ X51)
% 8.34/8.51          | ~ (r1_tarski @ X50 @ X52)
% 8.34/8.51          | (r1_tarski @ X50 @ (k1_tops_1 @ X51 @ X52))
% 8.34/8.51          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 8.34/8.51          | ~ (l1_pre_topc @ X51))),
% 8.34/8.51      inference('cnf', [status(esa)], [t56_tops_1])).
% 8.34/8.51  thf('7', plain,
% 8.34/8.51      (![X0 : $i]:
% 8.34/8.51         (~ (l1_pre_topc @ sk_A)
% 8.34/8.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.34/8.51          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 8.34/8.51          | ~ (r1_tarski @ sk_B_1 @ X0)
% 8.34/8.51          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 8.34/8.51      inference('sup-', [status(thm)], ['5', '6'])).
% 8.34/8.51  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('9', plain,
% 8.34/8.51      (![X0 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.34/8.51          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 8.34/8.51          | ~ (r1_tarski @ sk_B_1 @ X0)
% 8.34/8.51          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 8.34/8.51      inference('demod', [status(thm)], ['7', '8'])).
% 8.34/8.51  thf('10', plain,
% 8.34/8.51      ((![X0 : $i]:
% 8.34/8.51          (~ (r1_tarski @ sk_B_1 @ X0)
% 8.34/8.51           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 8.34/8.51           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 8.34/8.51         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['4', '9'])).
% 8.34/8.51  thf('11', plain,
% 8.34/8.51      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 8.34/8.51         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 8.34/8.51         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['2', '10'])).
% 8.34/8.51  thf(d10_xboole_0, axiom,
% 8.34/8.51    (![A:$i,B:$i]:
% 8.34/8.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.34/8.51  thf('12', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.34/8.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.34/8.51  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.34/8.51      inference('simplify', [status(thm)], ['12'])).
% 8.34/8.51  thf('14', plain,
% 8.34/8.51      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 8.34/8.51         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 8.34/8.51      inference('demod', [status(thm)], ['11', '13'])).
% 8.34/8.51  thf('15', plain,
% 8.34/8.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf(t44_tops_1, axiom,
% 8.34/8.51    (![A:$i]:
% 8.34/8.51     ( ( l1_pre_topc @ A ) =>
% 8.34/8.51       ( ![B:$i]:
% 8.34/8.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.34/8.51           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 8.34/8.51  thf('16', plain,
% 8.34/8.51      (![X48 : $i, X49 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 8.34/8.51          | (r1_tarski @ (k1_tops_1 @ X49 @ X48) @ X48)
% 8.34/8.51          | ~ (l1_pre_topc @ X49))),
% 8.34/8.51      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.34/8.51  thf('17', plain,
% 8.34/8.51      ((~ (l1_pre_topc @ sk_A)
% 8.34/8.51        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 8.34/8.51      inference('sup-', [status(thm)], ['15', '16'])).
% 8.34/8.51  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 8.34/8.51      inference('demod', [status(thm)], ['17', '18'])).
% 8.34/8.51  thf('20', plain,
% 8.34/8.51      (![X0 : $i, X2 : $i]:
% 8.34/8.51         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.34/8.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.34/8.51  thf('21', plain,
% 8.34/8.51      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 8.34/8.51        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['19', '20'])).
% 8.34/8.51  thf('22', plain,
% 8.34/8.51      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 8.34/8.51         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['14', '21'])).
% 8.34/8.51  thf('23', plain,
% 8.34/8.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf(l78_tops_1, axiom,
% 8.34/8.51    (![A:$i]:
% 8.34/8.51     ( ( l1_pre_topc @ A ) =>
% 8.34/8.51       ( ![B:$i]:
% 8.34/8.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.34/8.51           ( ( k2_tops_1 @ A @ B ) =
% 8.34/8.51             ( k7_subset_1 @
% 8.34/8.51               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 8.34/8.51               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.34/8.51  thf('24', plain,
% 8.34/8.51      (![X46 : $i, X47 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 8.34/8.51          | ((k2_tops_1 @ X47 @ X46)
% 8.34/8.51              = (k7_subset_1 @ (u1_struct_0 @ X47) @ 
% 8.34/8.51                 (k2_pre_topc @ X47 @ X46) @ (k1_tops_1 @ X47 @ X46)))
% 8.34/8.51          | ~ (l1_pre_topc @ X47))),
% 8.34/8.51      inference('cnf', [status(esa)], [l78_tops_1])).
% 8.34/8.51  thf('25', plain,
% 8.34/8.51      ((~ (l1_pre_topc @ sk_A)
% 8.34/8.51        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 8.34/8.51      inference('sup-', [status(thm)], ['23', '24'])).
% 8.34/8.51  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('27', plain,
% 8.34/8.51      (((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 8.34/8.51      inference('demod', [status(thm)], ['25', '26'])).
% 8.34/8.51  thf('28', plain,
% 8.34/8.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 8.34/8.51         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 8.34/8.51      inference('sup+', [status(thm)], ['22', '27'])).
% 8.34/8.51  thf('29', plain,
% 8.34/8.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 8.34/8.51         <= (~
% 8.34/8.51             (((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 8.34/8.51      inference('split', [status(esa)], ['0'])).
% 8.34/8.51  thf('30', plain,
% 8.34/8.51      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 8.34/8.51         <= (~
% 8.34/8.51             (((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 8.34/8.51             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['28', '29'])).
% 8.34/8.51  thf('31', plain,
% 8.34/8.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 8.34/8.51       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 8.34/8.51      inference('simplify', [status(thm)], ['30'])).
% 8.34/8.51  thf('32', plain,
% 8.34/8.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 8.34/8.51       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 8.34/8.51      inference('split', [status(esa)], ['3'])).
% 8.34/8.51  thf('33', plain,
% 8.34/8.51      (((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 8.34/8.51      inference('demod', [status(thm)], ['25', '26'])).
% 8.34/8.51  thf('34', plain,
% 8.34/8.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf(dt_k2_pre_topc, axiom,
% 8.34/8.51    (![A:$i,B:$i]:
% 8.34/8.51     ( ( ( l1_pre_topc @ A ) & 
% 8.34/8.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.34/8.51       ( m1_subset_1 @
% 8.34/8.51         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.34/8.51  thf('35', plain,
% 8.34/8.51      (![X42 : $i, X43 : $i]:
% 8.34/8.51         (~ (l1_pre_topc @ X42)
% 8.34/8.51          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 8.34/8.51          | (m1_subset_1 @ (k2_pre_topc @ X42 @ X43) @ 
% 8.34/8.51             (k1_zfmisc_1 @ (u1_struct_0 @ X42))))),
% 8.34/8.51      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 8.34/8.51  thf('36', plain,
% 8.34/8.51      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 8.34/8.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.34/8.51        | ~ (l1_pre_topc @ sk_A))),
% 8.34/8.51      inference('sup-', [status(thm)], ['34', '35'])).
% 8.34/8.51  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('38', plain,
% 8.34/8.51      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 8.34/8.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('demod', [status(thm)], ['36', '37'])).
% 8.34/8.51  thf(dt_k7_subset_1, axiom,
% 8.34/8.51    (![A:$i,B:$i,C:$i]:
% 8.34/8.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.34/8.51       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.34/8.51  thf('39', plain,
% 8.34/8.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 8.34/8.51          | (m1_subset_1 @ (k7_subset_1 @ X20 @ X19 @ X21) @ 
% 8.34/8.51             (k1_zfmisc_1 @ X20)))),
% 8.34/8.51      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 8.34/8.51  thf('40', plain,
% 8.34/8.51      (![X0 : $i]:
% 8.34/8.51         (m1_subset_1 @ 
% 8.34/8.51          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51           (k2_pre_topc @ sk_A @ sk_B_1) @ X0) @ 
% 8.34/8.51          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['38', '39'])).
% 8.34/8.51  thf('41', plain,
% 8.34/8.51      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 8.34/8.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('sup+', [status(thm)], ['33', '40'])).
% 8.34/8.51  thf('42', plain,
% 8.34/8.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf(redefinition_k4_subset_1, axiom,
% 8.34/8.51    (![A:$i,B:$i,C:$i]:
% 8.34/8.51     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 8.34/8.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.34/8.51       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 8.34/8.51  thf('43', plain,
% 8.34/8.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 8.34/8.51          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 8.34/8.51          | ((k4_subset_1 @ X29 @ X28 @ X30) = (k2_xboole_0 @ X28 @ X30)))),
% 8.34/8.51      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 8.34/8.51  thf('44', plain,
% 8.34/8.51      (![X0 : $i]:
% 8.34/8.51         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 8.34/8.51            = (k2_xboole_0 @ sk_B_1 @ X0))
% 8.34/8.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.34/8.51      inference('sup-', [status(thm)], ['42', '43'])).
% 8.34/8.51  thf('45', plain,
% 8.34/8.51      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 8.34/8.51         (k2_tops_1 @ sk_A @ sk_B_1))
% 8.34/8.51         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['41', '44'])).
% 8.34/8.51  thf('46', plain,
% 8.34/8.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf(t65_tops_1, axiom,
% 8.34/8.51    (![A:$i]:
% 8.34/8.51     ( ( l1_pre_topc @ A ) =>
% 8.34/8.51       ( ![B:$i]:
% 8.34/8.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.34/8.51           ( ( k2_pre_topc @ A @ B ) =
% 8.34/8.51             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.34/8.51  thf('47', plain,
% 8.34/8.51      (![X53 : $i, X54 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 8.34/8.51          | ((k2_pre_topc @ X54 @ X53)
% 8.34/8.51              = (k4_subset_1 @ (u1_struct_0 @ X54) @ X53 @ 
% 8.34/8.51                 (k2_tops_1 @ X54 @ X53)))
% 8.34/8.51          | ~ (l1_pre_topc @ X54))),
% 8.34/8.51      inference('cnf', [status(esa)], [t65_tops_1])).
% 8.34/8.51  thf('48', plain,
% 8.34/8.51      ((~ (l1_pre_topc @ sk_A)
% 8.34/8.51        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 8.34/8.51            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 8.34/8.51               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 8.34/8.51      inference('sup-', [status(thm)], ['46', '47'])).
% 8.34/8.51  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('50', plain,
% 8.34/8.51      (((k2_pre_topc @ sk_A @ sk_B_1)
% 8.34/8.51         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 8.34/8.51            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 8.34/8.51      inference('demod', [status(thm)], ['48', '49'])).
% 8.34/8.51  thf('51', plain,
% 8.34/8.51      (((k2_pre_topc @ sk_A @ sk_B_1)
% 8.34/8.51         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 8.34/8.51      inference('sup+', [status(thm)], ['45', '50'])).
% 8.34/8.51  thf(t46_xboole_1, axiom,
% 8.34/8.51    (![A:$i,B:$i]:
% 8.34/8.51     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 8.34/8.51  thf('52', plain,
% 8.34/8.51      (![X13 : $i, X14 : $i]:
% 8.34/8.51         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 8.34/8.51      inference('cnf', [status(esa)], [t46_xboole_1])).
% 8.34/8.51  thf(l32_xboole_1, axiom,
% 8.34/8.51    (![A:$i,B:$i]:
% 8.34/8.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.34/8.51  thf('53', plain,
% 8.34/8.51      (![X3 : $i, X4 : $i]:
% 8.34/8.51         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 8.34/8.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 8.34/8.51  thf('54', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         (((k1_xboole_0) != (k1_xboole_0))
% 8.34/8.51          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['52', '53'])).
% 8.34/8.51  thf('55', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 8.34/8.51      inference('simplify', [status(thm)], ['54'])).
% 8.34/8.51  thf(t3_subset, axiom,
% 8.34/8.51    (![A:$i,B:$i]:
% 8.34/8.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.34/8.51  thf('56', plain,
% 8.34/8.51      (![X39 : $i, X41 : $i]:
% 8.34/8.51         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 8.34/8.51      inference('cnf', [status(esa)], [t3_subset])).
% 8.34/8.51  thf('57', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['55', '56'])).
% 8.34/8.51  thf(d5_subset_1, axiom,
% 8.34/8.51    (![A:$i,B:$i]:
% 8.34/8.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.34/8.51       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 8.34/8.51  thf('58', plain,
% 8.34/8.51      (![X15 : $i, X16 : $i]:
% 8.34/8.51         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 8.34/8.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 8.34/8.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.34/8.51  thf('59', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 8.34/8.51           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 8.34/8.51      inference('sup-', [status(thm)], ['57', '58'])).
% 8.34/8.51  thf('60', plain,
% 8.34/8.51      (((k3_subset_1 @ (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 8.34/8.51         sk_B_1) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 8.34/8.51      inference('sup+', [status(thm)], ['51', '59'])).
% 8.34/8.51  thf('61', plain,
% 8.34/8.51      (((k2_pre_topc @ sk_A @ sk_B_1)
% 8.34/8.51         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 8.34/8.51      inference('sup+', [status(thm)], ['45', '50'])).
% 8.34/8.51  thf('62', plain,
% 8.34/8.51      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 8.34/8.51         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 8.34/8.51      inference('demod', [status(thm)], ['60', '61'])).
% 8.34/8.51  thf('63', plain,
% 8.34/8.51      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 8.34/8.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('demod', [status(thm)], ['36', '37'])).
% 8.34/8.51  thf(redefinition_k7_subset_1, axiom,
% 8.34/8.51    (![A:$i,B:$i,C:$i]:
% 8.34/8.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.34/8.51       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.34/8.51  thf('64', plain,
% 8.34/8.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 8.34/8.51          | ((k7_subset_1 @ X32 @ X31 @ X33) = (k4_xboole_0 @ X31 @ X33)))),
% 8.34/8.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.34/8.51  thf('65', plain,
% 8.34/8.51      (![X0 : $i]:
% 8.34/8.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 8.34/8.51           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 8.34/8.51      inference('sup-', [status(thm)], ['63', '64'])).
% 8.34/8.51  thf('66', plain,
% 8.34/8.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 8.34/8.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 8.34/8.51      inference('split', [status(esa)], ['3'])).
% 8.34/8.51  thf('67', plain,
% 8.34/8.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 8.34/8.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 8.34/8.51      inference('sup+', [status(thm)], ['65', '66'])).
% 8.34/8.51  thf('68', plain,
% 8.34/8.51      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          = (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 8.34/8.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 8.34/8.51      inference('sup+', [status(thm)], ['62', '67'])).
% 8.34/8.51  thf('69', plain,
% 8.34/8.51      (((k2_pre_topc @ sk_A @ sk_B_1)
% 8.34/8.51         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 8.34/8.51      inference('sup+', [status(thm)], ['45', '50'])).
% 8.34/8.51  thf('70', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['55', '56'])).
% 8.34/8.51  thf('71', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['55', '56'])).
% 8.34/8.51  thf(dt_k3_subset_1, axiom,
% 8.34/8.51    (![A:$i,B:$i]:
% 8.34/8.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.34/8.51       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.34/8.51  thf('72', plain,
% 8.34/8.51      (![X17 : $i, X18 : $i]:
% 8.34/8.51         ((m1_subset_1 @ (k3_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 8.34/8.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 8.34/8.51      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 8.34/8.51  thf('73', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         (m1_subset_1 @ (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 8.34/8.51          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['71', '72'])).
% 8.34/8.51  thf(t32_subset_1, axiom,
% 8.34/8.51    (![A:$i,B:$i]:
% 8.34/8.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.34/8.51       ( ![C:$i]:
% 8.34/8.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.34/8.51           ( ( k7_subset_1 @ A @ B @ C ) =
% 8.34/8.51             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 8.34/8.51  thf('74', plain,
% 8.34/8.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 8.34/8.51          | ((k7_subset_1 @ X35 @ X36 @ X34)
% 8.34/8.51              = (k9_subset_1 @ X35 @ X36 @ (k3_subset_1 @ X35 @ X34)))
% 8.34/8.51          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 8.34/8.51      inference('cnf', [status(esa)], [t32_subset_1])).
% 8.34/8.51  thf('75', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 8.34/8.51          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 8.34/8.51              (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 8.34/8.51              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 8.34/8.51                 (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 8.34/8.51                  (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)))))),
% 8.34/8.51      inference('sup-', [status(thm)], ['73', '74'])).
% 8.34/8.51  thf('76', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['55', '56'])).
% 8.34/8.51  thf(involutiveness_k3_subset_1, axiom,
% 8.34/8.51    (![A:$i,B:$i]:
% 8.34/8.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.34/8.51       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 8.34/8.51  thf('77', plain,
% 8.34/8.51      (![X26 : $i, X27 : $i]:
% 8.34/8.51         (((k3_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X26)) = (X26))
% 8.34/8.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 8.34/8.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.34/8.51  thf('78', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 8.34/8.51           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 8.34/8.51      inference('sup-', [status(thm)], ['76', '77'])).
% 8.34/8.51  thf('79', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 8.34/8.51          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 8.34/8.51              (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 8.34/8.51              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X1)))),
% 8.34/8.51      inference('demod', [status(thm)], ['75', '78'])).
% 8.34/8.51  thf('80', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ 
% 8.34/8.51           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 8.34/8.51           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ X1))),
% 8.34/8.51      inference('sup-', [status(thm)], ['70', '79'])).
% 8.34/8.51  thf('81', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 8.34/8.51      inference('sup-', [status(thm)], ['55', '56'])).
% 8.34/8.51  thf('82', plain,
% 8.34/8.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 8.34/8.51          | ((k7_subset_1 @ X32 @ X31 @ X33) = (k4_xboole_0 @ X31 @ X33)))),
% 8.34/8.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.34/8.51  thf('83', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.34/8.51         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ X2)
% 8.34/8.51           = (k4_xboole_0 @ X1 @ X2))),
% 8.34/8.51      inference('sup-', [status(thm)], ['81', '82'])).
% 8.34/8.51  thf('84', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.34/8.51      inference('simplify', [status(thm)], ['12'])).
% 8.34/8.51  thf('85', plain,
% 8.34/8.51      (![X39 : $i, X41 : $i]:
% 8.34/8.51         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 8.34/8.51      inference('cnf', [status(esa)], [t3_subset])).
% 8.34/8.51  thf('86', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.34/8.51      inference('sup-', [status(thm)], ['84', '85'])).
% 8.34/8.51  thf(idempotence_k9_subset_1, axiom,
% 8.34/8.51    (![A:$i,B:$i,C:$i]:
% 8.34/8.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.34/8.51       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 8.34/8.51  thf('87', plain,
% 8.34/8.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.34/8.51         (((k9_subset_1 @ X24 @ X23 @ X23) = (X23))
% 8.34/8.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 8.34/8.51      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 8.34/8.51  thf('88', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 8.34/8.51      inference('sup-', [status(thm)], ['86', '87'])).
% 8.34/8.51  thf('89', plain,
% 8.34/8.51      (![X0 : $i, X1 : $i]:
% 8.34/8.51         ((k4_xboole_0 @ X1 @ (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 8.34/8.51           = (X1))),
% 8.34/8.51      inference('demod', [status(thm)], ['80', '83', '88'])).
% 8.34/8.51  thf('90', plain,
% 8.34/8.51      (((k4_xboole_0 @ sk_B_1 @ 
% 8.34/8.51         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 8.34/8.51      inference('sup+', [status(thm)], ['69', '89'])).
% 8.34/8.51  thf('91', plain,
% 8.34/8.51      ((((k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 8.34/8.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 8.34/8.51      inference('sup+', [status(thm)], ['68', '90'])).
% 8.34/8.51  thf('92', plain,
% 8.34/8.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf(t74_tops_1, axiom,
% 8.34/8.51    (![A:$i]:
% 8.34/8.51     ( ( l1_pre_topc @ A ) =>
% 8.34/8.51       ( ![B:$i]:
% 8.34/8.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.34/8.51           ( ( k1_tops_1 @ A @ B ) =
% 8.34/8.51             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.34/8.51  thf('93', plain,
% 8.34/8.51      (![X55 : $i, X56 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 8.34/8.51          | ((k1_tops_1 @ X56 @ X55)
% 8.34/8.51              = (k7_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 8.34/8.51                 (k2_tops_1 @ X56 @ X55)))
% 8.34/8.51          | ~ (l1_pre_topc @ X56))),
% 8.34/8.51      inference('cnf', [status(esa)], [t74_tops_1])).
% 8.34/8.51  thf('94', plain,
% 8.34/8.51      ((~ (l1_pre_topc @ sk_A)
% 8.34/8.51        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 8.34/8.51               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 8.34/8.51      inference('sup-', [status(thm)], ['92', '93'])).
% 8.34/8.51  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('96', plain,
% 8.34/8.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('97', plain,
% 8.34/8.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.34/8.51         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 8.34/8.51          | ((k7_subset_1 @ X32 @ X31 @ X33) = (k4_xboole_0 @ X31 @ X33)))),
% 8.34/8.51      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.34/8.51  thf('98', plain,
% 8.34/8.51      (![X0 : $i]:
% 8.34/8.51         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 8.34/8.51           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 8.34/8.51      inference('sup-', [status(thm)], ['96', '97'])).
% 8.34/8.51  thf('99', plain,
% 8.34/8.51      (((k1_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 8.34/8.51      inference('demod', [status(thm)], ['94', '95', '98'])).
% 8.34/8.51  thf('100', plain,
% 8.34/8.51      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 8.34/8.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 8.34/8.51      inference('sup+', [status(thm)], ['91', '99'])).
% 8.34/8.51  thf('101', plain,
% 8.34/8.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf(fc9_tops_1, axiom,
% 8.34/8.51    (![A:$i,B:$i]:
% 8.34/8.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 8.34/8.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.34/8.51       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 8.34/8.51  thf('102', plain,
% 8.34/8.51      (![X44 : $i, X45 : $i]:
% 8.34/8.51         (~ (l1_pre_topc @ X44)
% 8.34/8.51          | ~ (v2_pre_topc @ X44)
% 8.34/8.51          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 8.34/8.51          | (v3_pre_topc @ (k1_tops_1 @ X44 @ X45) @ X44))),
% 8.34/8.51      inference('cnf', [status(esa)], [fc9_tops_1])).
% 8.34/8.51  thf('103', plain,
% 8.34/8.51      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 8.34/8.51        | ~ (v2_pre_topc @ sk_A)
% 8.34/8.51        | ~ (l1_pre_topc @ sk_A))),
% 8.34/8.51      inference('sup-', [status(thm)], ['101', '102'])).
% 8.34/8.51  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 8.34/8.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.34/8.51  thf('106', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 8.34/8.51      inference('demod', [status(thm)], ['103', '104', '105'])).
% 8.34/8.51  thf('107', plain,
% 8.34/8.51      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 8.34/8.51         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 8.34/8.51      inference('sup+', [status(thm)], ['100', '106'])).
% 8.34/8.51  thf('108', plain,
% 8.34/8.51      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 8.34/8.51      inference('split', [status(esa)], ['0'])).
% 8.34/8.51  thf('109', plain,
% 8.34/8.51      (~
% 8.34/8.51       (((k2_tops_1 @ sk_A @ sk_B_1)
% 8.34/8.51          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.34/8.51             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 8.34/8.51       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 8.34/8.51      inference('sup-', [status(thm)], ['107', '108'])).
% 8.34/8.51  thf('110', plain, ($false),
% 8.34/8.51      inference('sat_resolution*', [status(thm)], ['1', '31', '32', '109'])).
% 8.34/8.51  
% 8.34/8.51  % SZS output end Refutation
% 8.34/8.51  
% 8.34/8.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
