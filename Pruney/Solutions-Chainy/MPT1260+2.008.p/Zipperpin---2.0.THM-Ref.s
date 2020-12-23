%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NdrFszwcwT

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:23 EST 2020

% Result     : Theorem 27.65s
% Output     : Refutation 27.73s
% Verified   : 
% Statistics : Number of formulae       :  236 (1557 expanded)
%              Number of leaves         :   52 ( 547 expanded)
%              Depth                    :   22
%              Number of atoms          : 2116 (13714 expanded)
%              Number of equality atoms :  148 (1237 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ~ ( v3_pre_topc @ X62 @ X63 )
      | ~ ( r1_tarski @ X62 @ X64 )
      | ( r1_tarski @ X62 @ ( k1_tops_1 @ X63 @ X64 ) )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
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
    ! [X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X70 ) ) )
      | ( ( k1_tops_1 @ X70 @ X69 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X70 ) @ X69 @ ( k2_tops_1 @ X70 @ X69 ) ) )
      | ~ ( l1_pre_topc @ X70 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k7_subset_1 @ X46 @ X45 @ X47 )
        = ( k4_xboole_0 @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k7_subset_1 @ X46 @ X45 @ X47 )
        = ( k6_subset_1 @ X45 @ X47 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k6_subset_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X32: $i,X33: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k2_tops_1 @ X61 @ X60 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X61 ) @ ( k2_pre_topc @ X61 @ X60 ) @ ( k1_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('52',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('53',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('57',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('59',plain,(
    ! [X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('63',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','64'])).

thf('66',plain,(
    ! [X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('69',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('70',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('71',plain,(
    ! [X13: $i] :
      ( ( k6_subset_1 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','72'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('74',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('75',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('76',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k6_subset_1 @ X12 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( k6_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','77'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('79',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('81',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('82',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X51 @ X52 ) )
      = ( k3_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('83',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k6_subset_1 @ X19 @ X20 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( k6_subset_1 @ sk_B_1 @ k1_xboole_0 )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X13: $i] :
      ( ( k6_subset_1 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('86',plain,
    ( sk_B_1
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('88',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k6_subset_1 @ X19 @ X20 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('92',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('94',plain,
    ( sk_B_1
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('95',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('97',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( l1_pre_topc @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X56 @ X57 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X32: $i,X33: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('102',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k4_subset_1 @ X41 @ X40 @ X42 )
        = ( k2_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['95','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('107',plain,(
    ! [X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X68 ) ) )
      | ( ( k2_pre_topc @ X68 @ X67 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X68 ) @ X67 @ ( k2_tops_1 @ X68 @ X67 ) ) )
      | ~ ( l1_pre_topc @ X68 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('112',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['105','110','111'])).

thf('113',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('114',plain,(
    ! [X53: $i,X55: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( r1_tarski @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('116',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X39 @ ( k3_subset_1 @ X39 @ X38 ) )
        = X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('119',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('120',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k6_subset_1 @ X43 @ X44 )
      = ( k4_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('121',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k6_subset_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    ! [X32: $i,X33: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('124',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k6_subset_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('127',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k6_subset_1 @ X19 @ X20 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['117','122','125','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['112','131'])).

thf('133',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['105','110','111'])).

thf('134',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('136',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('137',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X30 @ X29 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('141',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k7_subset_1 @ X46 @ X45 @ X47 )
        = ( k6_subset_1 @ X45 @ X47 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('145',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['134','145'])).

thf('147',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['105','110','111'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference(demod,[status(thm)],['117','122','125','128'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('150',plain,(
    ! [X32: $i,X33: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('151',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ X49 ) )
      | ( ( k7_subset_1 @ X49 @ X50 @ X48 )
        = ( k9_subset_1 @ X49 @ X50 @ ( k3_subset_1 @ X49 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('154',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['149','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('157',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( ( k7_subset_1 @ X46 @ X45 @ X47 )
        = ( k6_subset_1 @ X45 @ X47 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ X2 )
      = ( k6_subset_1 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ X1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['155','158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['148','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('163',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('164',plain,(
    ! [X53: $i,X55: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X55 ) )
      | ~ ( r1_tarski @ X53 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('165',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('166',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k9_subset_1 @ X36 @ X35 @ X35 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['161','162','167'])).

thf('169',plain,
    ( ( k6_subset_1 @ sk_B_1 @ ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['147','168'])).

thf('170',plain,
    ( ( ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['146','169'])).

thf('171',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('172',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('174',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( l1_pre_topc @ X58 )
      | ~ ( v2_pre_topc @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X58 @ X59 ) @ X58 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('175',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['172','178'])).

thf('180',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('181',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','43','44','181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NdrFszwcwT
% 0.16/0.35  % Computer   : n024.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % DateTime   : Tue Dec  1 20:41:06 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.36  % Running in FO mode
% 27.65/27.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 27.65/27.91  % Solved by: fo/fo7.sh
% 27.65/27.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.65/27.91  % done 38005 iterations in 27.430s
% 27.65/27.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 27.65/27.91  % SZS output start Refutation
% 27.65/27.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 27.65/27.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 27.65/27.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 27.65/27.91  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 27.65/27.91  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 27.65/27.91  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 27.65/27.91  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 27.65/27.91  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 27.65/27.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 27.65/27.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 27.65/27.91  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 27.65/27.91  thf(sk_A_type, type, sk_A: $i).
% 27.65/27.91  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 27.65/27.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 27.65/27.91  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 27.65/27.91  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 27.65/27.91  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 27.65/27.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 27.65/27.91  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 27.65/27.91  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 27.65/27.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 27.65/27.91  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 27.65/27.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 27.65/27.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 27.65/27.91  thf(t76_tops_1, conjecture,
% 27.65/27.91    (![A:$i]:
% 27.65/27.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.65/27.91       ( ![B:$i]:
% 27.65/27.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.65/27.91           ( ( v3_pre_topc @ B @ A ) <=>
% 27.65/27.91             ( ( k2_tops_1 @ A @ B ) =
% 27.65/27.91               ( k7_subset_1 @
% 27.65/27.91                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 27.65/27.91  thf(zf_stmt_0, negated_conjecture,
% 27.65/27.91    (~( ![A:$i]:
% 27.65/27.91        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 27.65/27.91          ( ![B:$i]:
% 27.65/27.91            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.65/27.91              ( ( v3_pre_topc @ B @ A ) <=>
% 27.65/27.91                ( ( k2_tops_1 @ A @ B ) =
% 27.65/27.91                  ( k7_subset_1 @
% 27.65/27.91                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 27.65/27.91    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 27.65/27.91  thf('0', plain,
% 27.65/27.91      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 27.65/27.91        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf('1', plain,
% 27.65/27.91      (~
% 27.65/27.91       (((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 27.65/27.91       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 27.65/27.91      inference('split', [status(esa)], ['0'])).
% 27.65/27.91  thf('2', plain,
% 27.65/27.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf('3', plain,
% 27.65/27.91      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 27.65/27.91        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf('4', plain,
% 27.65/27.91      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 27.65/27.91      inference('split', [status(esa)], ['3'])).
% 27.65/27.91  thf('5', plain,
% 27.65/27.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf(t56_tops_1, axiom,
% 27.65/27.91    (![A:$i]:
% 27.65/27.91     ( ( l1_pre_topc @ A ) =>
% 27.65/27.91       ( ![B:$i]:
% 27.65/27.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.65/27.91           ( ![C:$i]:
% 27.65/27.91             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.65/27.91               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 27.65/27.91                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 27.65/27.91  thf('6', plain,
% 27.65/27.91      (![X62 : $i, X63 : $i, X64 : $i]:
% 27.65/27.91         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 27.65/27.91          | ~ (v3_pre_topc @ X62 @ X63)
% 27.65/27.91          | ~ (r1_tarski @ X62 @ X64)
% 27.65/27.91          | (r1_tarski @ X62 @ (k1_tops_1 @ X63 @ X64))
% 27.65/27.91          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 27.65/27.91          | ~ (l1_pre_topc @ X63))),
% 27.65/27.91      inference('cnf', [status(esa)], [t56_tops_1])).
% 27.65/27.91  thf('7', plain,
% 27.65/27.91      (![X0 : $i]:
% 27.65/27.91         (~ (l1_pre_topc @ sk_A)
% 27.65/27.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.65/27.91          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 27.65/27.91          | ~ (r1_tarski @ sk_B_1 @ X0)
% 27.65/27.91          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 27.65/27.91      inference('sup-', [status(thm)], ['5', '6'])).
% 27.65/27.91  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf('9', plain,
% 27.65/27.91      (![X0 : $i]:
% 27.65/27.91         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.65/27.91          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 27.65/27.91          | ~ (r1_tarski @ sk_B_1 @ X0)
% 27.65/27.91          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 27.65/27.91      inference('demod', [status(thm)], ['7', '8'])).
% 27.65/27.91  thf('10', plain,
% 27.65/27.91      ((![X0 : $i]:
% 27.65/27.91          (~ (r1_tarski @ sk_B_1 @ X0)
% 27.65/27.91           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 27.65/27.91           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 27.65/27.91         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 27.65/27.91      inference('sup-', [status(thm)], ['4', '9'])).
% 27.65/27.91  thf('11', plain,
% 27.65/27.91      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 27.65/27.91         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 27.65/27.91         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 27.65/27.91      inference('sup-', [status(thm)], ['2', '10'])).
% 27.65/27.91  thf(d10_xboole_0, axiom,
% 27.65/27.91    (![A:$i,B:$i]:
% 27.65/27.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 27.65/27.91  thf('12', plain,
% 27.65/27.91      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 27.65/27.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.65/27.91  thf('13', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 27.65/27.91      inference('simplify', [status(thm)], ['12'])).
% 27.65/27.91  thf('14', plain,
% 27.65/27.91      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 27.65/27.91         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 27.65/27.91      inference('demod', [status(thm)], ['11', '13'])).
% 27.65/27.91  thf('15', plain,
% 27.65/27.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf(t74_tops_1, axiom,
% 27.65/27.91    (![A:$i]:
% 27.65/27.91     ( ( l1_pre_topc @ A ) =>
% 27.65/27.91       ( ![B:$i]:
% 27.65/27.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.65/27.91           ( ( k1_tops_1 @ A @ B ) =
% 27.65/27.91             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 27.65/27.91  thf('16', plain,
% 27.65/27.91      (![X69 : $i, X70 : $i]:
% 27.65/27.91         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ X70)))
% 27.65/27.91          | ((k1_tops_1 @ X70 @ X69)
% 27.65/27.91              = (k7_subset_1 @ (u1_struct_0 @ X70) @ X69 @ 
% 27.65/27.91                 (k2_tops_1 @ X70 @ X69)))
% 27.65/27.91          | ~ (l1_pre_topc @ X70))),
% 27.65/27.91      inference('cnf', [status(esa)], [t74_tops_1])).
% 27.65/27.91  thf('17', plain,
% 27.65/27.91      ((~ (l1_pre_topc @ sk_A)
% 27.65/27.91        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 27.65/27.91               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 27.65/27.91      inference('sup-', [status(thm)], ['15', '16'])).
% 27.65/27.91  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf('19', plain,
% 27.65/27.91      (((k1_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 27.65/27.91            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.65/27.91      inference('demod', [status(thm)], ['17', '18'])).
% 27.65/27.91  thf('20', plain,
% 27.65/27.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf(redefinition_k7_subset_1, axiom,
% 27.65/27.91    (![A:$i,B:$i,C:$i]:
% 27.65/27.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 27.65/27.91       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 27.65/27.91  thf('21', plain,
% 27.65/27.91      (![X45 : $i, X46 : $i, X47 : $i]:
% 27.65/27.91         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 27.65/27.91          | ((k7_subset_1 @ X46 @ X45 @ X47) = (k4_xboole_0 @ X45 @ X47)))),
% 27.65/27.91      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 27.65/27.91  thf(redefinition_k6_subset_1, axiom,
% 27.65/27.91    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 27.65/27.91  thf('22', plain,
% 27.65/27.91      (![X43 : $i, X44 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 27.65/27.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.65/27.91  thf('23', plain,
% 27.65/27.91      (![X45 : $i, X46 : $i, X47 : $i]:
% 27.65/27.91         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 27.65/27.91          | ((k7_subset_1 @ X46 @ X45 @ X47) = (k6_subset_1 @ X45 @ X47)))),
% 27.65/27.91      inference('demod', [status(thm)], ['21', '22'])).
% 27.65/27.91  thf('24', plain,
% 27.65/27.91      (![X0 : $i]:
% 27.65/27.91         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 27.65/27.91           = (k6_subset_1 @ sk_B_1 @ X0))),
% 27.65/27.91      inference('sup-', [status(thm)], ['20', '23'])).
% 27.65/27.91  thf('25', plain,
% 27.65/27.91      (((k1_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.65/27.91      inference('demod', [status(thm)], ['19', '24'])).
% 27.65/27.91  thf(dt_k6_subset_1, axiom,
% 27.65/27.91    (![A:$i,B:$i]:
% 27.65/27.91     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 27.65/27.91  thf('26', plain,
% 27.65/27.91      (![X32 : $i, X33 : $i]:
% 27.65/27.91         (m1_subset_1 @ (k6_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))),
% 27.65/27.91      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 27.65/27.91  thf(t3_subset, axiom,
% 27.65/27.91    (![A:$i,B:$i]:
% 27.65/27.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 27.65/27.91  thf('27', plain,
% 27.65/27.91      (![X53 : $i, X54 : $i]:
% 27.65/27.91         ((r1_tarski @ X53 @ X54) | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54)))),
% 27.65/27.91      inference('cnf', [status(esa)], [t3_subset])).
% 27.65/27.91  thf('28', plain,
% 27.65/27.91      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 27.65/27.91      inference('sup-', [status(thm)], ['26', '27'])).
% 27.65/27.91  thf('29', plain,
% 27.65/27.91      (![X2 : $i, X4 : $i]:
% 27.65/27.91         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 27.65/27.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.65/27.91  thf('30', plain,
% 27.65/27.91      (![X0 : $i, X1 : $i]:
% 27.65/27.91         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 27.65/27.91          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 27.65/27.91      inference('sup-', [status(thm)], ['28', '29'])).
% 27.65/27.91  thf('31', plain,
% 27.65/27.91      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 27.65/27.91        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 27.65/27.91      inference('sup-', [status(thm)], ['25', '30'])).
% 27.65/27.91  thf('32', plain,
% 27.65/27.91      (((k1_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.65/27.91      inference('demod', [status(thm)], ['19', '24'])).
% 27.65/27.91  thf('33', plain,
% 27.65/27.91      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 27.65/27.91        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 27.65/27.91      inference('demod', [status(thm)], ['31', '32'])).
% 27.65/27.91  thf('34', plain,
% 27.65/27.91      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 27.65/27.91         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 27.65/27.91      inference('sup-', [status(thm)], ['14', '33'])).
% 27.65/27.91  thf('35', plain,
% 27.65/27.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf(l78_tops_1, axiom,
% 27.65/27.91    (![A:$i]:
% 27.65/27.91     ( ( l1_pre_topc @ A ) =>
% 27.65/27.91       ( ![B:$i]:
% 27.65/27.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.65/27.91           ( ( k2_tops_1 @ A @ B ) =
% 27.65/27.91             ( k7_subset_1 @
% 27.65/27.91               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 27.65/27.91               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 27.65/27.91  thf('36', plain,
% 27.65/27.91      (![X60 : $i, X61 : $i]:
% 27.65/27.91         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 27.65/27.91          | ((k2_tops_1 @ X61 @ X60)
% 27.65/27.91              = (k7_subset_1 @ (u1_struct_0 @ X61) @ 
% 27.65/27.91                 (k2_pre_topc @ X61 @ X60) @ (k1_tops_1 @ X61 @ X60)))
% 27.65/27.91          | ~ (l1_pre_topc @ X61))),
% 27.65/27.91      inference('cnf', [status(esa)], [l78_tops_1])).
% 27.65/27.91  thf('37', plain,
% 27.65/27.91      ((~ (l1_pre_topc @ sk_A)
% 27.65/27.91        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 27.65/27.91      inference('sup-', [status(thm)], ['35', '36'])).
% 27.65/27.91  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf('39', plain,
% 27.65/27.91      (((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 27.65/27.91      inference('demod', [status(thm)], ['37', '38'])).
% 27.65/27.91  thf('40', plain,
% 27.65/27.91      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 27.65/27.91         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 27.65/27.91      inference('sup+', [status(thm)], ['34', '39'])).
% 27.65/27.91  thf('41', plain,
% 27.65/27.91      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 27.65/27.91         <= (~
% 27.65/27.91             (((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 27.65/27.91      inference('split', [status(esa)], ['0'])).
% 27.65/27.91  thf('42', plain,
% 27.65/27.91      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 27.65/27.91         <= (~
% 27.65/27.91             (((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 27.65/27.91             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 27.65/27.91      inference('sup-', [status(thm)], ['40', '41'])).
% 27.65/27.91  thf('43', plain,
% 27.65/27.91      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 27.65/27.91       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 27.65/27.91      inference('simplify', [status(thm)], ['42'])).
% 27.65/27.91  thf('44', plain,
% 27.65/27.91      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.65/27.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 27.65/27.91       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 27.65/27.91      inference('split', [status(esa)], ['3'])).
% 27.65/27.91  thf(t7_xboole_1, axiom,
% 27.65/27.91    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 27.65/27.91  thf('45', plain,
% 27.65/27.91      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 27.65/27.91      inference('cnf', [status(esa)], [t7_xboole_1])).
% 27.65/27.91  thf('46', plain,
% 27.65/27.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf('47', plain,
% 27.65/27.91      (![X53 : $i, X54 : $i]:
% 27.65/27.91         ((r1_tarski @ X53 @ X54) | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X54)))),
% 27.65/27.91      inference('cnf', [status(esa)], [t3_subset])).
% 27.65/27.91  thf('48', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 27.65/27.91      inference('sup-', [status(thm)], ['46', '47'])).
% 27.65/27.91  thf(t1_xboole_1, axiom,
% 27.65/27.91    (![A:$i,B:$i,C:$i]:
% 27.65/27.91     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 27.65/27.91       ( r1_tarski @ A @ C ) ))).
% 27.65/27.91  thf('49', plain,
% 27.65/27.91      (![X7 : $i, X8 : $i, X9 : $i]:
% 27.65/27.91         (~ (r1_tarski @ X7 @ X8)
% 27.65/27.91          | ~ (r1_tarski @ X8 @ X9)
% 27.65/27.91          | (r1_tarski @ X7 @ X9))),
% 27.65/27.91      inference('cnf', [status(esa)], [t1_xboole_1])).
% 27.65/27.91  thf('50', plain,
% 27.65/27.91      (![X0 : $i]:
% 27.65/27.91         ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 27.65/27.91      inference('sup-', [status(thm)], ['48', '49'])).
% 27.65/27.91  thf('51', plain,
% 27.65/27.91      (![X0 : $i]:
% 27.65/27.91         (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 27.65/27.91      inference('sup-', [status(thm)], ['45', '50'])).
% 27.65/27.91  thf(t43_xboole_1, axiom,
% 27.65/27.91    (![A:$i,B:$i,C:$i]:
% 27.65/27.91     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 27.65/27.91       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 27.65/27.91  thf('52', plain,
% 27.65/27.91      (![X14 : $i, X15 : $i, X16 : $i]:
% 27.65/27.91         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 27.65/27.91          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 27.65/27.91      inference('cnf', [status(esa)], [t43_xboole_1])).
% 27.65/27.91  thf('53', plain,
% 27.65/27.91      (![X43 : $i, X44 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 27.65/27.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.65/27.91  thf('54', plain,
% 27.65/27.91      (![X14 : $i, X15 : $i, X16 : $i]:
% 27.65/27.91         ((r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X16)
% 27.65/27.91          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 27.65/27.91      inference('demod', [status(thm)], ['52', '53'])).
% 27.65/27.91  thf('55', plain,
% 27.65/27.91      (![X0 : $i]:
% 27.65/27.91         (r1_tarski @ (k6_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0)),
% 27.65/27.91      inference('sup-', [status(thm)], ['51', '54'])).
% 27.65/27.91  thf(commutativity_k2_tarski, axiom,
% 27.65/27.91    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 27.65/27.91  thf('56', plain,
% 27.65/27.91      (![X23 : $i, X24 : $i]:
% 27.65/27.91         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 27.65/27.91      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 27.65/27.91  thf(t2_boole, axiom,
% 27.65/27.91    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 27.65/27.91  thf('57', plain,
% 27.65/27.91      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 27.65/27.91      inference('cnf', [status(esa)], [t2_boole])).
% 27.65/27.91  thf(t12_setfam_1, axiom,
% 27.65/27.91    (![A:$i,B:$i]:
% 27.65/27.91     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 27.65/27.91  thf('58', plain,
% 27.65/27.91      (![X51 : $i, X52 : $i]:
% 27.65/27.91         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 27.65/27.91      inference('cnf', [status(esa)], [t12_setfam_1])).
% 27.65/27.91  thf('59', plain,
% 27.65/27.91      (![X10 : $i]:
% 27.65/27.91         ((k1_setfam_1 @ (k2_tarski @ X10 @ k1_xboole_0)) = (k1_xboole_0))),
% 27.65/27.91      inference('demod', [status(thm)], ['57', '58'])).
% 27.65/27.91  thf('60', plain,
% 27.65/27.91      (![X0 : $i]:
% 27.65/27.91         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 27.65/27.91      inference('sup+', [status(thm)], ['56', '59'])).
% 27.65/27.91  thf(t100_xboole_1, axiom,
% 27.65/27.91    (![A:$i,B:$i]:
% 27.65/27.91     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 27.65/27.91  thf('61', plain,
% 27.65/27.91      (![X5 : $i, X6 : $i]:
% 27.65/27.91         ((k4_xboole_0 @ X5 @ X6)
% 27.65/27.91           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 27.65/27.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 27.65/27.91  thf('62', plain,
% 27.65/27.91      (![X43 : $i, X44 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 27.65/27.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.65/27.91  thf('63', plain,
% 27.65/27.91      (![X51 : $i, X52 : $i]:
% 27.65/27.91         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 27.65/27.91      inference('cnf', [status(esa)], [t12_setfam_1])).
% 27.65/27.91  thf('64', plain,
% 27.65/27.91      (![X5 : $i, X6 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X5 @ X6)
% 27.65/27.91           = (k5_xboole_0 @ X5 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 27.65/27.91      inference('demod', [status(thm)], ['61', '62', '63'])).
% 27.65/27.91  thf('65', plain,
% 27.65/27.91      (![X0 : $i]:
% 27.65/27.91         ((k6_subset_1 @ k1_xboole_0 @ X0)
% 27.65/27.91           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 27.65/27.91      inference('sup+', [status(thm)], ['60', '64'])).
% 27.65/27.91  thf('66', plain,
% 27.65/27.91      (![X10 : $i]:
% 27.65/27.91         ((k1_setfam_1 @ (k2_tarski @ X10 @ k1_xboole_0)) = (k1_xboole_0))),
% 27.65/27.91      inference('demod', [status(thm)], ['57', '58'])).
% 27.65/27.91  thf('67', plain,
% 27.65/27.91      (![X5 : $i, X6 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X5 @ X6)
% 27.65/27.91           = (k5_xboole_0 @ X5 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 27.65/27.91      inference('demod', [status(thm)], ['61', '62', '63'])).
% 27.65/27.91  thf('68', plain,
% 27.65/27.91      (![X0 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 27.65/27.91      inference('sup+', [status(thm)], ['66', '67'])).
% 27.65/27.91  thf(t3_boole, axiom,
% 27.65/27.91    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 27.65/27.91  thf('69', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 27.65/27.91      inference('cnf', [status(esa)], [t3_boole])).
% 27.65/27.91  thf('70', plain,
% 27.65/27.91      (![X43 : $i, X44 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 27.65/27.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.65/27.91  thf('71', plain, (![X13 : $i]: ((k6_subset_1 @ X13 @ k1_xboole_0) = (X13))),
% 27.65/27.91      inference('demod', [status(thm)], ['69', '70'])).
% 27.65/27.91  thf('72', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 27.65/27.91      inference('sup+', [status(thm)], ['68', '71'])).
% 27.65/27.91  thf('73', plain,
% 27.65/27.91      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 27.65/27.91      inference('demod', [status(thm)], ['65', '72'])).
% 27.65/27.91  thf(t38_xboole_1, axiom,
% 27.65/27.91    (![A:$i,B:$i]:
% 27.65/27.91     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 27.65/27.91       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 27.65/27.91  thf('74', plain,
% 27.65/27.91      (![X11 : $i, X12 : $i]:
% 27.65/27.91         (((X11) = (k1_xboole_0))
% 27.65/27.91          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 27.65/27.91      inference('cnf', [status(esa)], [t38_xboole_1])).
% 27.65/27.91  thf('75', plain,
% 27.65/27.91      (![X43 : $i, X44 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 27.65/27.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.65/27.91  thf('76', plain,
% 27.65/27.91      (![X11 : $i, X12 : $i]:
% 27.65/27.91         (((X11) = (k1_xboole_0))
% 27.65/27.91          | ~ (r1_tarski @ X11 @ (k6_subset_1 @ X12 @ X11)))),
% 27.65/27.91      inference('demod', [status(thm)], ['74', '75'])).
% 27.65/27.91  thf('77', plain,
% 27.65/27.91      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 27.65/27.91      inference('sup-', [status(thm)], ['73', '76'])).
% 27.65/27.91  thf('78', plain,
% 27.65/27.91      (((k6_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 27.65/27.91      inference('sup-', [status(thm)], ['55', '77'])).
% 27.65/27.91  thf(t48_xboole_1, axiom,
% 27.65/27.91    (![A:$i,B:$i]:
% 27.65/27.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 27.65/27.91  thf('79', plain,
% 27.65/27.91      (![X19 : $i, X20 : $i]:
% 27.65/27.91         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 27.65/27.91           = (k3_xboole_0 @ X19 @ X20))),
% 27.65/27.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 27.65/27.91  thf('80', plain,
% 27.65/27.91      (![X43 : $i, X44 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 27.65/27.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.65/27.91  thf('81', plain,
% 27.65/27.91      (![X43 : $i, X44 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 27.65/27.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.65/27.91  thf('82', plain,
% 27.65/27.91      (![X51 : $i, X52 : $i]:
% 27.65/27.91         ((k1_setfam_1 @ (k2_tarski @ X51 @ X52)) = (k3_xboole_0 @ X51 @ X52))),
% 27.65/27.91      inference('cnf', [status(esa)], [t12_setfam_1])).
% 27.65/27.91  thf('83', plain,
% 27.65/27.91      (![X19 : $i, X20 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X19 @ (k6_subset_1 @ X19 @ X20))
% 27.65/27.91           = (k1_setfam_1 @ (k2_tarski @ X19 @ X20)))),
% 27.65/27.91      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 27.65/27.91  thf('84', plain,
% 27.65/27.91      (((k6_subset_1 @ sk_B_1 @ k1_xboole_0)
% 27.65/27.91         = (k1_setfam_1 @ (k2_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.65/27.91      inference('sup+', [status(thm)], ['78', '83'])).
% 27.65/27.91  thf('85', plain, (![X13 : $i]: ((k6_subset_1 @ X13 @ k1_xboole_0) = (X13))),
% 27.65/27.91      inference('demod', [status(thm)], ['69', '70'])).
% 27.65/27.91  thf('86', plain,
% 27.65/27.91      (((sk_B_1) = (k1_setfam_1 @ (k2_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.65/27.91      inference('demod', [status(thm)], ['84', '85'])).
% 27.65/27.91  thf('87', plain,
% 27.65/27.91      (![X23 : $i, X24 : $i]:
% 27.65/27.91         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 27.65/27.91      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 27.65/27.91  thf('88', plain,
% 27.65/27.91      (![X5 : $i, X6 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X5 @ X6)
% 27.65/27.91           = (k5_xboole_0 @ X5 @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6))))),
% 27.65/27.91      inference('demod', [status(thm)], ['61', '62', '63'])).
% 27.65/27.91  thf('89', plain,
% 27.65/27.91      (![X0 : $i, X1 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X0 @ X1)
% 27.65/27.91           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 27.65/27.91      inference('sup+', [status(thm)], ['87', '88'])).
% 27.65/27.91  thf('90', plain,
% 27.65/27.91      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 27.65/27.91         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 27.65/27.91      inference('sup+', [status(thm)], ['86', '89'])).
% 27.65/27.91  thf('91', plain,
% 27.65/27.91      (![X19 : $i, X20 : $i]:
% 27.65/27.91         ((k6_subset_1 @ X19 @ (k6_subset_1 @ X19 @ X20))
% 27.65/27.91           = (k1_setfam_1 @ (k2_tarski @ X19 @ X20)))),
% 27.65/27.91      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 27.65/27.91  thf('92', plain,
% 27.65/27.91      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 27.65/27.91         = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 27.65/27.91      inference('sup+', [status(thm)], ['90', '91'])).
% 27.65/27.91  thf('93', plain,
% 27.65/27.91      (![X23 : $i, X24 : $i]:
% 27.65/27.91         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 27.65/27.91      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 27.65/27.91  thf('94', plain,
% 27.65/27.91      (((sk_B_1) = (k1_setfam_1 @ (k2_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))))),
% 27.65/27.91      inference('demod', [status(thm)], ['84', '85'])).
% 27.65/27.91  thf('95', plain,
% 27.65/27.91      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.65/27.91         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 27.65/27.91      inference('demod', [status(thm)], ['92', '93', '94'])).
% 27.65/27.91  thf('96', plain,
% 27.65/27.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf(dt_k2_tops_1, axiom,
% 27.65/27.91    (![A:$i,B:$i]:
% 27.65/27.91     ( ( ( l1_pre_topc @ A ) & 
% 27.65/27.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 27.65/27.91       ( m1_subset_1 @
% 27.65/27.91         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 27.65/27.91  thf('97', plain,
% 27.65/27.91      (![X56 : $i, X57 : $i]:
% 27.65/27.91         (~ (l1_pre_topc @ X56)
% 27.65/27.91          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 27.65/27.91          | (m1_subset_1 @ (k2_tops_1 @ X56 @ X57) @ 
% 27.65/27.91             (k1_zfmisc_1 @ (u1_struct_0 @ X56))))),
% 27.65/27.91      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 27.65/27.91  thf('98', plain,
% 27.65/27.91      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 27.65/27.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.65/27.91        | ~ (l1_pre_topc @ sk_A))),
% 27.65/27.91      inference('sup-', [status(thm)], ['96', '97'])).
% 27.65/27.91  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 27.65/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.65/27.91  thf('100', plain,
% 27.65/27.91      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 27.65/27.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.65/27.91      inference('demod', [status(thm)], ['98', '99'])).
% 27.65/27.91  thf('101', plain,
% 27.65/27.91      (![X32 : $i, X33 : $i]:
% 27.65/27.91         (m1_subset_1 @ (k6_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))),
% 27.65/27.91      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 27.65/27.91  thf(redefinition_k4_subset_1, axiom,
% 27.65/27.91    (![A:$i,B:$i,C:$i]:
% 27.65/27.91     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 27.65/27.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 27.65/27.91       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 27.65/27.91  thf('102', plain,
% 27.65/27.91      (![X40 : $i, X41 : $i, X42 : $i]:
% 27.65/27.91         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 27.65/27.91          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41))
% 27.65/27.91          | ((k4_subset_1 @ X41 @ X40 @ X42) = (k2_xboole_0 @ X40 @ X42)))),
% 27.65/27.91      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 27.65/27.91  thf('103', plain,
% 27.65/27.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.65/27.91         (((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 27.65/27.91            = (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X2))
% 27.65/27.91          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 27.73/27.91      inference('sup-', [status(thm)], ['101', '102'])).
% 27.73/27.91  thf('104', plain,
% 27.73/27.91      (![X0 : $i]:
% 27.73/27.91         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 27.73/27.91           (k2_tops_1 @ sk_A @ sk_B_1))
% 27.73/27.91           = (k2_xboole_0 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 27.73/27.91              (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.73/27.91      inference('sup-', [status(thm)], ['100', '103'])).
% 27.73/27.91  thf('105', plain,
% 27.73/27.91      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 27.73/27.91         (k2_tops_1 @ sk_A @ sk_B_1))
% 27.73/27.91         = (k2_xboole_0 @ 
% 27.73/27.91            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 27.73/27.91            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.73/27.91      inference('sup+', [status(thm)], ['95', '104'])).
% 27.73/27.91  thf('106', plain,
% 27.73/27.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.73/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.73/27.91  thf(t65_tops_1, axiom,
% 27.73/27.91    (![A:$i]:
% 27.73/27.91     ( ( l1_pre_topc @ A ) =>
% 27.73/27.91       ( ![B:$i]:
% 27.73/27.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 27.73/27.91           ( ( k2_pre_topc @ A @ B ) =
% 27.73/27.91             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 27.73/27.91  thf('107', plain,
% 27.73/27.91      (![X67 : $i, X68 : $i]:
% 27.73/27.91         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (u1_struct_0 @ X68)))
% 27.73/27.91          | ((k2_pre_topc @ X68 @ X67)
% 27.73/27.91              = (k4_subset_1 @ (u1_struct_0 @ X68) @ X67 @ 
% 27.73/27.91                 (k2_tops_1 @ X68 @ X67)))
% 27.73/27.91          | ~ (l1_pre_topc @ X68))),
% 27.73/27.91      inference('cnf', [status(esa)], [t65_tops_1])).
% 27.73/27.91  thf('108', plain,
% 27.73/27.91      ((~ (l1_pre_topc @ sk_A)
% 27.73/27.91        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 27.73/27.91            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 27.73/27.91               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 27.73/27.91      inference('sup-', [status(thm)], ['106', '107'])).
% 27.73/27.91  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 27.73/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.73/27.91  thf('110', plain,
% 27.73/27.91      (((k2_pre_topc @ sk_A @ sk_B_1)
% 27.73/27.91         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 27.73/27.91            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.73/27.91      inference('demod', [status(thm)], ['108', '109'])).
% 27.73/27.91  thf('111', plain,
% 27.73/27.91      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 27.73/27.91      inference('demod', [status(thm)], ['92', '93', '94'])).
% 27.73/27.91  thf('112', plain,
% 27.73/27.91      (((k2_pre_topc @ sk_A @ sk_B_1)
% 27.73/27.91         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.73/27.91      inference('demod', [status(thm)], ['105', '110', '111'])).
% 27.73/27.91  thf('113', plain,
% 27.73/27.91      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 27.73/27.91      inference('cnf', [status(esa)], [t7_xboole_1])).
% 27.73/27.91  thf('114', plain,
% 27.73/27.91      (![X53 : $i, X55 : $i]:
% 27.73/27.91         ((m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X53 @ X55))),
% 27.73/27.91      inference('cnf', [status(esa)], [t3_subset])).
% 27.73/27.91  thf('115', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 27.73/27.91      inference('sup-', [status(thm)], ['113', '114'])).
% 27.73/27.91  thf(involutiveness_k3_subset_1, axiom,
% 27.73/27.91    (![A:$i,B:$i]:
% 27.73/27.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 27.73/27.91       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 27.73/27.91  thf('116', plain,
% 27.73/27.91      (![X38 : $i, X39 : $i]:
% 27.73/27.91         (((k3_subset_1 @ X39 @ (k3_subset_1 @ X39 @ X38)) = (X38))
% 27.73/27.91          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 27.73/27.91      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 27.73/27.91  thf('117', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 27.73/27.91           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 27.73/27.91      inference('sup-', [status(thm)], ['115', '116'])).
% 27.73/27.91  thf('118', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 27.73/27.91      inference('sup-', [status(thm)], ['113', '114'])).
% 27.73/27.91  thf(d5_subset_1, axiom,
% 27.73/27.91    (![A:$i,B:$i]:
% 27.73/27.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 27.73/27.91       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 27.73/27.91  thf('119', plain,
% 27.73/27.91      (![X25 : $i, X26 : $i]:
% 27.73/27.91         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 27.73/27.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 27.73/27.91      inference('cnf', [status(esa)], [d5_subset_1])).
% 27.73/27.91  thf('120', plain,
% 27.73/27.91      (![X43 : $i, X44 : $i]:
% 27.73/27.91         ((k6_subset_1 @ X43 @ X44) = (k4_xboole_0 @ X43 @ X44))),
% 27.73/27.91      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 27.73/27.91  thf('121', plain,
% 27.73/27.91      (![X25 : $i, X26 : $i]:
% 27.73/27.91         (((k3_subset_1 @ X25 @ X26) = (k6_subset_1 @ X25 @ X26))
% 27.73/27.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 27.73/27.91      inference('demod', [status(thm)], ['119', '120'])).
% 27.73/27.91  thf('122', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 27.73/27.91           = (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 27.73/27.91      inference('sup-', [status(thm)], ['118', '121'])).
% 27.73/27.91  thf('123', plain,
% 27.73/27.91      (![X32 : $i, X33 : $i]:
% 27.73/27.91         (m1_subset_1 @ (k6_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))),
% 27.73/27.91      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 27.73/27.91  thf('124', plain,
% 27.73/27.91      (![X25 : $i, X26 : $i]:
% 27.73/27.91         (((k3_subset_1 @ X25 @ X26) = (k6_subset_1 @ X25 @ X26))
% 27.73/27.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 27.73/27.91      inference('demod', [status(thm)], ['119', '120'])).
% 27.73/27.91  thf('125', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 27.73/27.91           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 27.73/27.91      inference('sup-', [status(thm)], ['123', '124'])).
% 27.73/27.91  thf('126', plain,
% 27.73/27.91      (![X23 : $i, X24 : $i]:
% 27.73/27.91         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 27.73/27.91      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 27.73/27.91  thf('127', plain,
% 27.73/27.91      (![X19 : $i, X20 : $i]:
% 27.73/27.91         ((k6_subset_1 @ X19 @ (k6_subset_1 @ X19 @ X20))
% 27.73/27.91           = (k1_setfam_1 @ (k2_tarski @ X19 @ X20)))),
% 27.73/27.91      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 27.73/27.91  thf('128', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 27.73/27.91           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 27.73/27.91      inference('sup+', [status(thm)], ['126', '127'])).
% 27.73/27.91  thf('129', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))) = (X1))),
% 27.73/27.91      inference('demod', [status(thm)], ['117', '122', '125', '128'])).
% 27.73/27.91  thf('130', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k6_subset_1 @ X0 @ X1)
% 27.73/27.91           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 27.73/27.91      inference('sup+', [status(thm)], ['87', '88'])).
% 27.73/27.91  thf('131', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 27.73/27.91           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 27.73/27.91      inference('sup+', [status(thm)], ['129', '130'])).
% 27.73/27.91  thf('132', plain,
% 27.73/27.91      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 27.73/27.91         = (k5_xboole_0 @ 
% 27.73/27.91            (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) @ sk_B_1))),
% 27.73/27.91      inference('sup+', [status(thm)], ['112', '131'])).
% 27.73/27.91  thf('133', plain,
% 27.73/27.91      (((k2_pre_topc @ sk_A @ sk_B_1)
% 27.73/27.91         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.73/27.91      inference('demod', [status(thm)], ['105', '110', '111'])).
% 27.73/27.91  thf('134', plain,
% 27.73/27.91      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 27.73/27.91         = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 27.73/27.91      inference('demod', [status(thm)], ['132', '133'])).
% 27.73/27.91  thf('135', plain,
% 27.73/27.91      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 27.73/27.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.73/27.91      inference('demod', [status(thm)], ['98', '99'])).
% 27.73/27.91  thf('136', plain,
% 27.73/27.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.73/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.73/27.91  thf(dt_k4_subset_1, axiom,
% 27.73/27.91    (![A:$i,B:$i,C:$i]:
% 27.73/27.91     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 27.73/27.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 27.73/27.91       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 27.73/27.91  thf('137', plain,
% 27.73/27.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 27.73/27.91         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 27.73/27.91          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 27.73/27.91          | (m1_subset_1 @ (k4_subset_1 @ X30 @ X29 @ X31) @ 
% 27.73/27.91             (k1_zfmisc_1 @ X30)))),
% 27.73/27.91      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 27.73/27.91  thf('138', plain,
% 27.73/27.91      (![X0 : $i]:
% 27.73/27.91         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 27.73/27.91           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 27.73/27.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 27.73/27.91      inference('sup-', [status(thm)], ['136', '137'])).
% 27.73/27.91  thf('139', plain,
% 27.73/27.91      ((m1_subset_1 @ 
% 27.73/27.91        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 27.73/27.91         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 27.73/27.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.73/27.91      inference('sup-', [status(thm)], ['135', '138'])).
% 27.73/27.91  thf('140', plain,
% 27.73/27.91      (((k2_pre_topc @ sk_A @ sk_B_1)
% 27.73/27.91         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 27.73/27.91            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.73/27.91      inference('demod', [status(thm)], ['108', '109'])).
% 27.73/27.91  thf('141', plain,
% 27.73/27.91      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 27.73/27.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.73/27.91      inference('demod', [status(thm)], ['139', '140'])).
% 27.73/27.91  thf('142', plain,
% 27.73/27.91      (![X45 : $i, X46 : $i, X47 : $i]:
% 27.73/27.91         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 27.73/27.91          | ((k7_subset_1 @ X46 @ X45 @ X47) = (k6_subset_1 @ X45 @ X47)))),
% 27.73/27.91      inference('demod', [status(thm)], ['21', '22'])).
% 27.73/27.91  thf('143', plain,
% 27.73/27.91      (![X0 : $i]:
% 27.73/27.91         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 27.73/27.91           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 27.73/27.91      inference('sup-', [status(thm)], ['141', '142'])).
% 27.73/27.91  thf('144', plain,
% 27.73/27.91      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 27.73/27.91         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 27.73/27.91      inference('split', [status(esa)], ['3'])).
% 27.73/27.91  thf('145', plain,
% 27.73/27.91      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 27.73/27.91         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 27.73/27.91      inference('sup+', [status(thm)], ['143', '144'])).
% 27.73/27.91  thf('146', plain,
% 27.73/27.91      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91          = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 27.73/27.91         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 27.73/27.91      inference('sup+', [status(thm)], ['134', '145'])).
% 27.73/27.91  thf('147', plain,
% 27.73/27.91      (((k2_pre_topc @ sk_A @ sk_B_1)
% 27.73/27.91         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.73/27.91      inference('demod', [status(thm)], ['105', '110', '111'])).
% 27.73/27.91  thf('148', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k1_setfam_1 @ (k2_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))) = (X1))),
% 27.73/27.91      inference('demod', [status(thm)], ['117', '122', '125', '128'])).
% 27.73/27.91  thf('149', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 27.73/27.91      inference('sup-', [status(thm)], ['113', '114'])).
% 27.73/27.91  thf('150', plain,
% 27.73/27.91      (![X32 : $i, X33 : $i]:
% 27.73/27.91         (m1_subset_1 @ (k6_subset_1 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))),
% 27.73/27.91      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 27.73/27.91  thf(t32_subset_1, axiom,
% 27.73/27.91    (![A:$i,B:$i]:
% 27.73/27.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 27.73/27.91       ( ![C:$i]:
% 27.73/27.91         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 27.73/27.91           ( ( k7_subset_1 @ A @ B @ C ) =
% 27.73/27.91             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 27.73/27.91  thf('151', plain,
% 27.73/27.91      (![X48 : $i, X49 : $i, X50 : $i]:
% 27.73/27.91         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ X49))
% 27.73/27.91          | ((k7_subset_1 @ X49 @ X50 @ X48)
% 27.73/27.91              = (k9_subset_1 @ X49 @ X50 @ (k3_subset_1 @ X49 @ X48)))
% 27.73/27.91          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X49)))),
% 27.73/27.91      inference('cnf', [status(esa)], [t32_subset_1])).
% 27.73/27.91  thf('152', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.73/27.91         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 27.73/27.91          | ((k7_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 27.73/27.91              = (k9_subset_1 @ X0 @ X2 @ 
% 27.73/27.91                 (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))))),
% 27.73/27.91      inference('sup-', [status(thm)], ['150', '151'])).
% 27.73/27.91  thf('153', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 27.73/27.91           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 27.73/27.91      inference('sup-', [status(thm)], ['123', '124'])).
% 27.73/27.91  thf('154', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.73/27.91         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 27.73/27.91          | ((k7_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 27.73/27.91              = (k9_subset_1 @ X0 @ X2 @ 
% 27.73/27.91                 (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))))),
% 27.73/27.91      inference('demod', [status(thm)], ['152', '153'])).
% 27.73/27.91  thf('155', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.73/27.91         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ 
% 27.73/27.91           (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 27.73/27.91           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ 
% 27.73/27.91              (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 27.73/27.91               (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2))))),
% 27.73/27.91      inference('sup-', [status(thm)], ['149', '154'])).
% 27.73/27.91  thf('156', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 27.73/27.91      inference('sup-', [status(thm)], ['113', '114'])).
% 27.73/27.91  thf('157', plain,
% 27.73/27.91      (![X45 : $i, X46 : $i, X47 : $i]:
% 27.73/27.91         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 27.73/27.91          | ((k7_subset_1 @ X46 @ X45 @ X47) = (k6_subset_1 @ X45 @ X47)))),
% 27.73/27.91      inference('demod', [status(thm)], ['21', '22'])).
% 27.73/27.91  thf('158', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.73/27.91         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ X2)
% 27.73/27.91           = (k6_subset_1 @ X1 @ X2))),
% 27.73/27.91      inference('sup-', [status(thm)], ['156', '157'])).
% 27.73/27.91  thf('159', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 27.73/27.91           = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 27.73/27.91      inference('sup+', [status(thm)], ['126', '127'])).
% 27.73/27.91  thf('160', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.73/27.91         ((k6_subset_1 @ X1 @ (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 27.73/27.91           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ 
% 27.73/27.91              (k1_setfam_1 @ (k2_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 27.73/27.91      inference('demod', [status(thm)], ['155', '158', '159'])).
% 27.73/27.91  thf('161', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k6_subset_1 @ X0 @ (k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 27.73/27.91           = (k9_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0 @ X0))),
% 27.73/27.91      inference('sup+', [status(thm)], ['148', '160'])).
% 27.73/27.91  thf('162', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 27.73/27.91           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 27.73/27.91      inference('sup+', [status(thm)], ['129', '130'])).
% 27.73/27.91  thf('163', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 27.73/27.91      inference('simplify', [status(thm)], ['12'])).
% 27.73/27.91  thf('164', plain,
% 27.73/27.91      (![X53 : $i, X55 : $i]:
% 27.73/27.91         ((m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X55)) | ~ (r1_tarski @ X53 @ X55))),
% 27.73/27.91      inference('cnf', [status(esa)], [t3_subset])).
% 27.73/27.91  thf('165', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 27.73/27.91      inference('sup-', [status(thm)], ['163', '164'])).
% 27.73/27.91  thf(idempotence_k9_subset_1, axiom,
% 27.73/27.91    (![A:$i,B:$i,C:$i]:
% 27.73/27.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 27.73/27.91       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 27.73/27.91  thf('166', plain,
% 27.73/27.91      (![X35 : $i, X36 : $i, X37 : $i]:
% 27.73/27.91         (((k9_subset_1 @ X36 @ X35 @ X35) = (X35))
% 27.73/27.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 27.73/27.91      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 27.73/27.91  thf('167', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 27.73/27.91      inference('sup-', [status(thm)], ['165', '166'])).
% 27.73/27.91  thf('168', plain,
% 27.73/27.91      (![X0 : $i, X1 : $i]:
% 27.73/27.91         ((k6_subset_1 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))
% 27.73/27.91           = (X0))),
% 27.73/27.91      inference('demod', [status(thm)], ['161', '162', '167'])).
% 27.73/27.91  thf('169', plain,
% 27.73/27.91      (((k6_subset_1 @ sk_B_1 @ 
% 27.73/27.91         (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 27.73/27.91      inference('sup+', [status(thm)], ['147', '168'])).
% 27.73/27.91  thf('170', plain,
% 27.73/27.91      ((((k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 27.73/27.91         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 27.73/27.91      inference('sup+', [status(thm)], ['146', '169'])).
% 27.73/27.91  thf('171', plain,
% 27.73/27.91      (((k1_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 27.73/27.91      inference('demod', [status(thm)], ['19', '24'])).
% 27.73/27.91  thf('172', plain,
% 27.73/27.91      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 27.73/27.91         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 27.73/27.91      inference('sup+', [status(thm)], ['170', '171'])).
% 27.73/27.91  thf('173', plain,
% 27.73/27.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 27.73/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.73/27.91  thf(fc9_tops_1, axiom,
% 27.73/27.91    (![A:$i,B:$i]:
% 27.73/27.91     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 27.73/27.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 27.73/27.91       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 27.73/27.91  thf('174', plain,
% 27.73/27.91      (![X58 : $i, X59 : $i]:
% 27.73/27.91         (~ (l1_pre_topc @ X58)
% 27.73/27.91          | ~ (v2_pre_topc @ X58)
% 27.73/27.91          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 27.73/27.91          | (v3_pre_topc @ (k1_tops_1 @ X58 @ X59) @ X58))),
% 27.73/27.91      inference('cnf', [status(esa)], [fc9_tops_1])).
% 27.73/27.91  thf('175', plain,
% 27.73/27.91      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 27.73/27.91        | ~ (v2_pre_topc @ sk_A)
% 27.73/27.91        | ~ (l1_pre_topc @ sk_A))),
% 27.73/27.91      inference('sup-', [status(thm)], ['173', '174'])).
% 27.73/27.91  thf('176', plain, ((v2_pre_topc @ sk_A)),
% 27.73/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.73/27.91  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 27.73/27.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.73/27.91  thf('178', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 27.73/27.91      inference('demod', [status(thm)], ['175', '176', '177'])).
% 27.73/27.91  thf('179', plain,
% 27.73/27.91      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 27.73/27.91         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 27.73/27.91      inference('sup+', [status(thm)], ['172', '178'])).
% 27.73/27.91  thf('180', plain,
% 27.73/27.91      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 27.73/27.91      inference('split', [status(esa)], ['0'])).
% 27.73/27.91  thf('181', plain,
% 27.73/27.91      (~
% 27.73/27.91       (((k2_tops_1 @ sk_A @ sk_B_1)
% 27.73/27.91          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 27.73/27.91             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 27.73/27.91       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 27.73/27.91      inference('sup-', [status(thm)], ['179', '180'])).
% 27.73/27.91  thf('182', plain, ($false),
% 27.73/27.91      inference('sat_resolution*', [status(thm)], ['1', '43', '44', '181'])).
% 27.73/27.91  
% 27.73/27.91  % SZS output end Refutation
% 27.73/27.91  
% 27.73/27.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
