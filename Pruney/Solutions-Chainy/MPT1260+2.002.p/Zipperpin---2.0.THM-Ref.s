%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iJaGxn6mUx

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:22 EST 2020

% Result     : Theorem 16.29s
% Output     : Refutation 16.29s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 293 expanded)
%              Number of leaves         :   45 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          : 1392 (3277 expanded)
%              Number of equality atoms :  105 ( 226 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

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
    ! [X79: $i,X80: $i,X81: $i] :
      ( ~ ( m1_subset_1 @ X79 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X80 ) ) )
      | ~ ( v3_pre_topc @ X79 @ X80 )
      | ~ ( r1_tarski @ X79 @ X81 )
      | ( r1_tarski @ X79 @ ( k1_tops_1 @ X80 @ X81 ) )
      | ~ ( m1_subset_1 @ X81 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X80 ) ) )
      | ~ ( l1_pre_topc @ X80 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
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
    ! [X86: $i,X87: $i] :
      ( ~ ( m1_subset_1 @ X86 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X87 ) ) )
      | ( ( k1_tops_1 @ X87 @ X86 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X87 ) @ X86 @ ( k2_tops_1 @ X87 @ X86 ) ) )
      | ~ ( l1_pre_topc @ X87 ) ) ),
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
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k7_subset_1 @ X63 @ X62 @ X64 )
        = ( k4_xboole_0 @ X62 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k6_subset_1 @ X60 @ X61 )
      = ( k4_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k7_subset_1 @ X63 @ X62 @ X64 )
        = ( k6_subset_1 @ X62 @ X64 ) ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('27',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k6_subset_1 @ X60 @ X61 )
      = ( k4_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X18 @ X19 ) @ X18 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
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
    ! [X77: $i,X78: $i] :
      ( ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X78 ) ) )
      | ( ( k2_tops_1 @ X78 @ X77 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X78 ) @ ( k2_pre_topc @ X78 @ X77 ) @ ( k1_tops_1 @ X78 @ X77 ) ) )
      | ~ ( l1_pre_topc @ X78 ) ) ),
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

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X73: $i,X74: $i] :
      ( ~ ( l1_pre_topc @ X73 )
      | ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X73 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X73 @ X74 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X73 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X44 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X44 @ X43 @ X45 ) @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('55',plain,(
    ! [X84: $i,X85: $i] :
      ( ~ ( m1_subset_1 @ X84 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X85 ) ) )
      | ( ( k2_pre_topc @ X85 @ X84 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X85 ) @ X84 @ ( k2_tops_1 @ X85 @ X84 ) ) )
      | ~ ( l1_pre_topc @ X85 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X63 ) )
      | ( ( k7_subset_1 @ X63 @ X62 @ X64 )
        = ( k6_subset_1 @ X62 @ X64 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('64',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k6_subset_1 @ X60 @ X61 )
      = ( k4_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('69',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X34 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X32 @ X33 ) @ ( k3_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('70',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k6_subset_1 @ X60 @ X61 )
      = ( k4_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('71',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k6_subset_1 @ X60 @ X61 )
      = ( k4_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('72',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k6_subset_1 @ X60 @ X61 )
      = ( k4_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('73',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k6_subset_1 @ X32 @ ( k6_subset_1 @ X33 @ X34 ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ X32 @ X33 ) @ ( k3_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('75',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k4_xboole_0 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('76',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k6_subset_1 @ X60 @ X61 )
      = ( k4_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('77',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k6_subset_1 @ X2 @ ( k6_subset_1 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X0 ) @ ( k5_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','79'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('81',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_tarski @ X38 @ X37 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('82',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X68 @ X69 ) )
      = ( k3_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X68 @ X69 ) )
      = ( k3_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('86',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('87',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k6_subset_1 @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('91',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('92',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k6_subset_1 @ X60 @ X61 )
      = ( k4_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('93',plain,(
    ! [X22: $i] :
      ( ( k6_subset_1 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','85','90','93'])).

thf('95',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('98',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('99',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( r1_tarski @ X23 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X22: $i] :
      ( ( k6_subset_1 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['96','105'])).

thf('107',plain,
    ( ( ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['63','106'])).

thf('108',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('109',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('111',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( l1_pre_topc @ X75 )
      | ~ ( v2_pre_topc @ X75 )
      | ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X75 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X75 @ X76 ) @ X75 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('112',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['109','115'])).

thf('117',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','43','44','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iJaGxn6mUx
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 16.29/16.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 16.29/16.49  % Solved by: fo/fo7.sh
% 16.29/16.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.29/16.49  % done 26246 iterations in 16.028s
% 16.29/16.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 16.29/16.49  % SZS output start Refutation
% 16.29/16.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 16.29/16.49  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 16.29/16.49  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 16.29/16.49  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 16.29/16.49  thf(sk_A_type, type, sk_A: $i).
% 16.29/16.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 16.29/16.49  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 16.29/16.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 16.29/16.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 16.29/16.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 16.29/16.49  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 16.29/16.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 16.29/16.49  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 16.29/16.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 16.29/16.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 16.29/16.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 16.29/16.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 16.29/16.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 16.29/16.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 16.29/16.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 16.29/16.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 16.29/16.49  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 16.29/16.49  thf(t76_tops_1, conjecture,
% 16.29/16.49    (![A:$i]:
% 16.29/16.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.29/16.49       ( ![B:$i]:
% 16.29/16.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.29/16.49           ( ( v3_pre_topc @ B @ A ) <=>
% 16.29/16.49             ( ( k2_tops_1 @ A @ B ) =
% 16.29/16.49               ( k7_subset_1 @
% 16.29/16.49                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 16.29/16.49  thf(zf_stmt_0, negated_conjecture,
% 16.29/16.49    (~( ![A:$i]:
% 16.29/16.49        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.29/16.49          ( ![B:$i]:
% 16.29/16.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.29/16.49              ( ( v3_pre_topc @ B @ A ) <=>
% 16.29/16.49                ( ( k2_tops_1 @ A @ B ) =
% 16.29/16.49                  ( k7_subset_1 @
% 16.29/16.49                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 16.29/16.49    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 16.29/16.49  thf('0', plain,
% 16.29/16.49      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 16.29/16.49        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf('1', plain,
% 16.29/16.49      (~
% 16.29/16.49       (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 16.29/16.49       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.29/16.49      inference('split', [status(esa)], ['0'])).
% 16.29/16.49  thf('2', plain,
% 16.29/16.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf('3', plain,
% 16.29/16.49      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 16.29/16.49        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf('4', plain,
% 16.29/16.49      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.29/16.49      inference('split', [status(esa)], ['3'])).
% 16.29/16.49  thf('5', plain,
% 16.29/16.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf(t56_tops_1, axiom,
% 16.29/16.49    (![A:$i]:
% 16.29/16.49     ( ( l1_pre_topc @ A ) =>
% 16.29/16.49       ( ![B:$i]:
% 16.29/16.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.29/16.49           ( ![C:$i]:
% 16.29/16.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.29/16.49               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 16.29/16.49                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 16.29/16.49  thf('6', plain,
% 16.29/16.49      (![X79 : $i, X80 : $i, X81 : $i]:
% 16.29/16.49         (~ (m1_subset_1 @ X79 @ (k1_zfmisc_1 @ (u1_struct_0 @ X80)))
% 16.29/16.49          | ~ (v3_pre_topc @ X79 @ X80)
% 16.29/16.49          | ~ (r1_tarski @ X79 @ X81)
% 16.29/16.49          | (r1_tarski @ X79 @ (k1_tops_1 @ X80 @ X81))
% 16.29/16.49          | ~ (m1_subset_1 @ X81 @ (k1_zfmisc_1 @ (u1_struct_0 @ X80)))
% 16.29/16.49          | ~ (l1_pre_topc @ X80))),
% 16.29/16.49      inference('cnf', [status(esa)], [t56_tops_1])).
% 16.29/16.49  thf('7', plain,
% 16.29/16.49      (![X0 : $i]:
% 16.29/16.49         (~ (l1_pre_topc @ sk_A)
% 16.29/16.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.29/16.49          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 16.29/16.49          | ~ (r1_tarski @ sk_B_1 @ X0)
% 16.29/16.49          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.29/16.49      inference('sup-', [status(thm)], ['5', '6'])).
% 16.29/16.49  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf('9', plain,
% 16.29/16.49      (![X0 : $i]:
% 16.29/16.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.29/16.49          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 16.29/16.49          | ~ (r1_tarski @ sk_B_1 @ X0)
% 16.29/16.49          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.29/16.49      inference('demod', [status(thm)], ['7', '8'])).
% 16.29/16.49  thf('10', plain,
% 16.29/16.49      ((![X0 : $i]:
% 16.29/16.49          (~ (r1_tarski @ sk_B_1 @ X0)
% 16.29/16.49           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 16.29/16.49           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 16.29/16.49         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.29/16.49      inference('sup-', [status(thm)], ['4', '9'])).
% 16.29/16.49  thf('11', plain,
% 16.29/16.49      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 16.29/16.49         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 16.29/16.49         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.29/16.49      inference('sup-', [status(thm)], ['2', '10'])).
% 16.29/16.49  thf(d10_xboole_0, axiom,
% 16.29/16.49    (![A:$i,B:$i]:
% 16.29/16.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 16.29/16.49  thf('12', plain,
% 16.29/16.49      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 16.29/16.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.29/16.49  thf('13', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 16.29/16.49      inference('simplify', [status(thm)], ['12'])).
% 16.29/16.49  thf('14', plain,
% 16.29/16.49      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 16.29/16.49         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.29/16.49      inference('demod', [status(thm)], ['11', '13'])).
% 16.29/16.49  thf('15', plain,
% 16.29/16.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf(t74_tops_1, axiom,
% 16.29/16.49    (![A:$i]:
% 16.29/16.49     ( ( l1_pre_topc @ A ) =>
% 16.29/16.49       ( ![B:$i]:
% 16.29/16.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.29/16.49           ( ( k1_tops_1 @ A @ B ) =
% 16.29/16.49             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 16.29/16.49  thf('16', plain,
% 16.29/16.49      (![X86 : $i, X87 : $i]:
% 16.29/16.49         (~ (m1_subset_1 @ X86 @ (k1_zfmisc_1 @ (u1_struct_0 @ X87)))
% 16.29/16.49          | ((k1_tops_1 @ X87 @ X86)
% 16.29/16.49              = (k7_subset_1 @ (u1_struct_0 @ X87) @ X86 @ 
% 16.29/16.49                 (k2_tops_1 @ X87 @ X86)))
% 16.29/16.49          | ~ (l1_pre_topc @ X87))),
% 16.29/16.49      inference('cnf', [status(esa)], [t74_tops_1])).
% 16.29/16.49  thf('17', plain,
% 16.29/16.49      ((~ (l1_pre_topc @ sk_A)
% 16.29/16.49        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.29/16.49               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 16.29/16.49      inference('sup-', [status(thm)], ['15', '16'])).
% 16.29/16.49  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf('19', plain,
% 16.29/16.49      (((k1_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.29/16.49            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.29/16.49      inference('demod', [status(thm)], ['17', '18'])).
% 16.29/16.49  thf('20', plain,
% 16.29/16.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf(redefinition_k7_subset_1, axiom,
% 16.29/16.49    (![A:$i,B:$i,C:$i]:
% 16.29/16.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 16.29/16.49       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 16.29/16.49  thf('21', plain,
% 16.29/16.49      (![X62 : $i, X63 : $i, X64 : $i]:
% 16.29/16.49         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 16.29/16.49          | ((k7_subset_1 @ X63 @ X62 @ X64) = (k4_xboole_0 @ X62 @ X64)))),
% 16.29/16.49      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 16.29/16.49  thf(redefinition_k6_subset_1, axiom,
% 16.29/16.49    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 16.29/16.49  thf('22', plain,
% 16.29/16.49      (![X60 : $i, X61 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))),
% 16.29/16.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.29/16.49  thf('23', plain,
% 16.29/16.49      (![X62 : $i, X63 : $i, X64 : $i]:
% 16.29/16.49         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 16.29/16.49          | ((k7_subset_1 @ X63 @ X62 @ X64) = (k6_subset_1 @ X62 @ X64)))),
% 16.29/16.49      inference('demod', [status(thm)], ['21', '22'])).
% 16.29/16.49  thf('24', plain,
% 16.29/16.49      (![X0 : $i]:
% 16.29/16.49         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 16.29/16.49           = (k6_subset_1 @ sk_B_1 @ X0))),
% 16.29/16.49      inference('sup-', [status(thm)], ['20', '23'])).
% 16.29/16.49  thf('25', plain,
% 16.29/16.49      (((k1_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.29/16.49      inference('demod', [status(thm)], ['19', '24'])).
% 16.29/16.49  thf(t36_xboole_1, axiom,
% 16.29/16.49    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 16.29/16.49  thf('26', plain,
% 16.29/16.49      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 16.29/16.49      inference('cnf', [status(esa)], [t36_xboole_1])).
% 16.29/16.49  thf('27', plain,
% 16.29/16.49      (![X60 : $i, X61 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))),
% 16.29/16.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.29/16.49  thf('28', plain,
% 16.29/16.49      (![X18 : $i, X19 : $i]: (r1_tarski @ (k6_subset_1 @ X18 @ X19) @ X18)),
% 16.29/16.49      inference('demod', [status(thm)], ['26', '27'])).
% 16.29/16.49  thf('29', plain,
% 16.29/16.49      (![X7 : $i, X9 : $i]:
% 16.29/16.49         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 16.29/16.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.29/16.49  thf('30', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i]:
% 16.29/16.49         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 16.29/16.49          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 16.29/16.49      inference('sup-', [status(thm)], ['28', '29'])).
% 16.29/16.49  thf('31', plain,
% 16.29/16.49      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 16.29/16.49        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 16.29/16.49      inference('sup-', [status(thm)], ['25', '30'])).
% 16.29/16.49  thf('32', plain,
% 16.29/16.49      (((k1_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.29/16.49      inference('demod', [status(thm)], ['19', '24'])).
% 16.29/16.49  thf('33', plain,
% 16.29/16.49      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 16.29/16.49        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 16.29/16.49      inference('demod', [status(thm)], ['31', '32'])).
% 16.29/16.49  thf('34', plain,
% 16.29/16.49      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 16.29/16.49         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.29/16.49      inference('sup-', [status(thm)], ['14', '33'])).
% 16.29/16.49  thf('35', plain,
% 16.29/16.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf(l78_tops_1, axiom,
% 16.29/16.49    (![A:$i]:
% 16.29/16.49     ( ( l1_pre_topc @ A ) =>
% 16.29/16.49       ( ![B:$i]:
% 16.29/16.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.29/16.49           ( ( k2_tops_1 @ A @ B ) =
% 16.29/16.49             ( k7_subset_1 @
% 16.29/16.49               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 16.29/16.49               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 16.29/16.49  thf('36', plain,
% 16.29/16.49      (![X77 : $i, X78 : $i]:
% 16.29/16.49         (~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ (u1_struct_0 @ X78)))
% 16.29/16.49          | ((k2_tops_1 @ X78 @ X77)
% 16.29/16.49              = (k7_subset_1 @ (u1_struct_0 @ X78) @ 
% 16.29/16.49                 (k2_pre_topc @ X78 @ X77) @ (k1_tops_1 @ X78 @ X77)))
% 16.29/16.49          | ~ (l1_pre_topc @ X78))),
% 16.29/16.49      inference('cnf', [status(esa)], [l78_tops_1])).
% 16.29/16.49  thf('37', plain,
% 16.29/16.49      ((~ (l1_pre_topc @ sk_A)
% 16.29/16.49        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 16.29/16.49      inference('sup-', [status(thm)], ['35', '36'])).
% 16.29/16.49  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf('39', plain,
% 16.29/16.49      (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 16.29/16.49      inference('demod', [status(thm)], ['37', '38'])).
% 16.29/16.49  thf('40', plain,
% 16.29/16.49      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 16.29/16.49         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.29/16.49      inference('sup+', [status(thm)], ['34', '39'])).
% 16.29/16.49  thf('41', plain,
% 16.29/16.49      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 16.29/16.49         <= (~
% 16.29/16.49             (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.29/16.49      inference('split', [status(esa)], ['0'])).
% 16.29/16.49  thf('42', plain,
% 16.29/16.49      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 16.29/16.49         <= (~
% 16.29/16.49             (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 16.29/16.49             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.29/16.49      inference('sup-', [status(thm)], ['40', '41'])).
% 16.29/16.49  thf('43', plain,
% 16.29/16.49      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 16.29/16.49       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.29/16.49      inference('simplify', [status(thm)], ['42'])).
% 16.29/16.49  thf('44', plain,
% 16.29/16.49      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 16.29/16.49       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.29/16.49      inference('split', [status(esa)], ['3'])).
% 16.29/16.49  thf('45', plain,
% 16.29/16.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf(dt_k2_tops_1, axiom,
% 16.29/16.49    (![A:$i,B:$i]:
% 16.29/16.49     ( ( ( l1_pre_topc @ A ) & 
% 16.29/16.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.29/16.49       ( m1_subset_1 @
% 16.29/16.49         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 16.29/16.49  thf('46', plain,
% 16.29/16.49      (![X73 : $i, X74 : $i]:
% 16.29/16.49         (~ (l1_pre_topc @ X73)
% 16.29/16.49          | ~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (u1_struct_0 @ X73)))
% 16.29/16.49          | (m1_subset_1 @ (k2_tops_1 @ X73 @ X74) @ 
% 16.29/16.49             (k1_zfmisc_1 @ (u1_struct_0 @ X73))))),
% 16.29/16.49      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 16.29/16.49  thf('47', plain,
% 16.29/16.49      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 16.29/16.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.29/16.49        | ~ (l1_pre_topc @ sk_A))),
% 16.29/16.49      inference('sup-', [status(thm)], ['45', '46'])).
% 16.29/16.49  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf('49', plain,
% 16.29/16.49      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 16.29/16.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('demod', [status(thm)], ['47', '48'])).
% 16.29/16.49  thf('50', plain,
% 16.29/16.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf(dt_k4_subset_1, axiom,
% 16.29/16.49    (![A:$i,B:$i,C:$i]:
% 16.29/16.49     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 16.29/16.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 16.29/16.49       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 16.29/16.49  thf('51', plain,
% 16.29/16.49      (![X43 : $i, X44 : $i, X45 : $i]:
% 16.29/16.49         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 16.29/16.49          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X44))
% 16.29/16.49          | (m1_subset_1 @ (k4_subset_1 @ X44 @ X43 @ X45) @ 
% 16.29/16.49             (k1_zfmisc_1 @ X44)))),
% 16.29/16.49      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 16.29/16.49  thf('52', plain,
% 16.29/16.49      (![X0 : $i]:
% 16.29/16.49         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 16.29/16.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.29/16.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.29/16.49      inference('sup-', [status(thm)], ['50', '51'])).
% 16.29/16.49  thf('53', plain,
% 16.29/16.49      ((m1_subset_1 @ 
% 16.29/16.49        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.29/16.49         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 16.29/16.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('sup-', [status(thm)], ['49', '52'])).
% 16.29/16.49  thf('54', plain,
% 16.29/16.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf(t65_tops_1, axiom,
% 16.29/16.49    (![A:$i]:
% 16.29/16.49     ( ( l1_pre_topc @ A ) =>
% 16.29/16.49       ( ![B:$i]:
% 16.29/16.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.29/16.49           ( ( k2_pre_topc @ A @ B ) =
% 16.29/16.49             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 16.29/16.49  thf('55', plain,
% 16.29/16.49      (![X84 : $i, X85 : $i]:
% 16.29/16.49         (~ (m1_subset_1 @ X84 @ (k1_zfmisc_1 @ (u1_struct_0 @ X85)))
% 16.29/16.49          | ((k2_pre_topc @ X85 @ X84)
% 16.29/16.49              = (k4_subset_1 @ (u1_struct_0 @ X85) @ X84 @ 
% 16.29/16.49                 (k2_tops_1 @ X85 @ X84)))
% 16.29/16.49          | ~ (l1_pre_topc @ X85))),
% 16.29/16.49      inference('cnf', [status(esa)], [t65_tops_1])).
% 16.29/16.49  thf('56', plain,
% 16.29/16.49      ((~ (l1_pre_topc @ sk_A)
% 16.29/16.49        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 16.29/16.49            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.29/16.49               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 16.29/16.49      inference('sup-', [status(thm)], ['54', '55'])).
% 16.29/16.49  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf('58', plain,
% 16.29/16.49      (((k2_pre_topc @ sk_A @ sk_B_1)
% 16.29/16.49         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.29/16.49            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.29/16.49      inference('demod', [status(thm)], ['56', '57'])).
% 16.29/16.49  thf('59', plain,
% 16.29/16.49      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.29/16.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('demod', [status(thm)], ['53', '58'])).
% 16.29/16.49  thf('60', plain,
% 16.29/16.49      (![X62 : $i, X63 : $i, X64 : $i]:
% 16.29/16.49         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X63))
% 16.29/16.49          | ((k7_subset_1 @ X63 @ X62 @ X64) = (k6_subset_1 @ X62 @ X64)))),
% 16.29/16.49      inference('demod', [status(thm)], ['21', '22'])).
% 16.29/16.49  thf('61', plain,
% 16.29/16.49      (![X0 : $i]:
% 16.29/16.49         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 16.29/16.49           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 16.29/16.49      inference('sup-', [status(thm)], ['59', '60'])).
% 16.29/16.49  thf('62', plain,
% 16.29/16.49      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 16.29/16.49         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.29/16.49      inference('split', [status(esa)], ['3'])).
% 16.29/16.49  thf('63', plain,
% 16.29/16.49      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 16.29/16.49         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.29/16.49      inference('sup+', [status(thm)], ['61', '62'])).
% 16.29/16.49  thf(idempotence_k3_xboole_0, axiom,
% 16.29/16.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 16.29/16.49  thf('64', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 16.29/16.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 16.29/16.49  thf(t100_xboole_1, axiom,
% 16.29/16.49    (![A:$i,B:$i]:
% 16.29/16.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 16.29/16.49  thf('65', plain,
% 16.29/16.49      (![X10 : $i, X11 : $i]:
% 16.29/16.49         ((k4_xboole_0 @ X10 @ X11)
% 16.29/16.49           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 16.29/16.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 16.29/16.49  thf('66', plain,
% 16.29/16.49      (![X60 : $i, X61 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))),
% 16.29/16.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.29/16.49  thf('67', plain,
% 16.29/16.49      (![X10 : $i, X11 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X10 @ X11)
% 16.29/16.49           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 16.29/16.49      inference('demod', [status(thm)], ['65', '66'])).
% 16.29/16.49  thf('68', plain,
% 16.29/16.49      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 16.29/16.49      inference('sup+', [status(thm)], ['64', '67'])).
% 16.29/16.49  thf(t52_xboole_1, axiom,
% 16.29/16.49    (![A:$i,B:$i,C:$i]:
% 16.29/16.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 16.29/16.49       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 16.29/16.49  thf('69', plain,
% 16.29/16.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 16.29/16.49         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X34))
% 16.29/16.49           = (k2_xboole_0 @ (k4_xboole_0 @ X32 @ X33) @ 
% 16.29/16.49              (k3_xboole_0 @ X32 @ X34)))),
% 16.29/16.49      inference('cnf', [status(esa)], [t52_xboole_1])).
% 16.29/16.49  thf('70', plain,
% 16.29/16.49      (![X60 : $i, X61 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))),
% 16.29/16.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.29/16.49  thf('71', plain,
% 16.29/16.49      (![X60 : $i, X61 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))),
% 16.29/16.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.29/16.49  thf('72', plain,
% 16.29/16.49      (![X60 : $i, X61 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))),
% 16.29/16.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.29/16.49  thf('73', plain,
% 16.29/16.49      (![X32 : $i, X33 : $i, X34 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X32 @ (k6_subset_1 @ X33 @ X34))
% 16.29/16.49           = (k2_xboole_0 @ (k6_subset_1 @ X32 @ X33) @ 
% 16.29/16.49              (k3_xboole_0 @ X32 @ X34)))),
% 16.29/16.49      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 16.29/16.49  thf(commutativity_k2_xboole_0, axiom,
% 16.29/16.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 16.29/16.49  thf('74', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.29/16.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 16.29/16.49  thf(t46_xboole_1, axiom,
% 16.29/16.49    (![A:$i,B:$i]:
% 16.29/16.49     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 16.29/16.49  thf('75', plain,
% 16.29/16.49      (![X30 : $i, X31 : $i]:
% 16.29/16.49         ((k4_xboole_0 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 16.29/16.49      inference('cnf', [status(esa)], [t46_xboole_1])).
% 16.29/16.49  thf('76', plain,
% 16.29/16.49      (![X60 : $i, X61 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))),
% 16.29/16.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.29/16.49  thf('77', plain,
% 16.29/16.49      (![X30 : $i, X31 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 16.29/16.49      inference('demod', [status(thm)], ['75', '76'])).
% 16.29/16.49  thf('78', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 16.29/16.49      inference('sup+', [status(thm)], ['74', '77'])).
% 16.29/16.49  thf('79', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.29/16.49         ((k6_subset_1 @ (k3_xboole_0 @ X2 @ X0) @ 
% 16.29/16.49           (k6_subset_1 @ X2 @ (k6_subset_1 @ X1 @ X0))) = (k1_xboole_0))),
% 16.29/16.49      inference('sup+', [status(thm)], ['73', '78'])).
% 16.29/16.49  thf('80', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i]:
% 16.29/16.49         ((k6_subset_1 @ (k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X0) @ 
% 16.29/16.49           (k5_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))
% 16.29/16.49           = (k1_xboole_0))),
% 16.29/16.49      inference('sup+', [status(thm)], ['68', '79'])).
% 16.29/16.49  thf(commutativity_k2_tarski, axiom,
% 16.29/16.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 16.29/16.49  thf('81', plain,
% 16.29/16.49      (![X37 : $i, X38 : $i]:
% 16.29/16.49         ((k2_tarski @ X38 @ X37) = (k2_tarski @ X37 @ X38))),
% 16.29/16.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 16.29/16.49  thf(t12_setfam_1, axiom,
% 16.29/16.49    (![A:$i,B:$i]:
% 16.29/16.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 16.29/16.49  thf('82', plain,
% 16.29/16.49      (![X68 : $i, X69 : $i]:
% 16.29/16.49         ((k1_setfam_1 @ (k2_tarski @ X68 @ X69)) = (k3_xboole_0 @ X68 @ X69))),
% 16.29/16.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 16.29/16.49  thf('83', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i]:
% 16.29/16.49         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 16.29/16.49      inference('sup+', [status(thm)], ['81', '82'])).
% 16.29/16.49  thf('84', plain,
% 16.29/16.49      (![X68 : $i, X69 : $i]:
% 16.29/16.49         ((k1_setfam_1 @ (k2_tarski @ X68 @ X69)) = (k3_xboole_0 @ X68 @ X69))),
% 16.29/16.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 16.29/16.49  thf('85', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.29/16.49      inference('sup+', [status(thm)], ['83', '84'])).
% 16.29/16.49  thf(t1_boole, axiom,
% 16.29/16.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 16.29/16.49  thf('86', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 16.29/16.49      inference('cnf', [status(esa)], [t1_boole])).
% 16.29/16.49  thf('87', plain,
% 16.29/16.49      (![X30 : $i, X31 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X30 @ (k2_xboole_0 @ X30 @ X31)) = (k1_xboole_0))),
% 16.29/16.49      inference('demod', [status(thm)], ['75', '76'])).
% 16.29/16.49  thf('88', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 16.29/16.49      inference('sup+', [status(thm)], ['86', '87'])).
% 16.29/16.49  thf('89', plain,
% 16.29/16.49      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 16.29/16.49      inference('sup+', [status(thm)], ['64', '67'])).
% 16.29/16.49  thf('90', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 16.29/16.49      inference('demod', [status(thm)], ['88', '89'])).
% 16.29/16.49  thf(t3_boole, axiom,
% 16.29/16.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 16.29/16.49  thf('91', plain, (![X22 : $i]: ((k4_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 16.29/16.49      inference('cnf', [status(esa)], [t3_boole])).
% 16.29/16.49  thf('92', plain,
% 16.29/16.49      (![X60 : $i, X61 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))),
% 16.29/16.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.29/16.49  thf('93', plain, (![X22 : $i]: ((k6_subset_1 @ X22 @ k1_xboole_0) = (X22))),
% 16.29/16.49      inference('demod', [status(thm)], ['91', '92'])).
% 16.29/16.49  thf('94', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i]:
% 16.29/16.49         ((k3_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)) = (k1_xboole_0))),
% 16.29/16.49      inference('demod', [status(thm)], ['80', '85', '90', '93'])).
% 16.29/16.49  thf('95', plain,
% 16.29/16.49      (![X10 : $i, X11 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X10 @ X11)
% 16.29/16.49           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 16.29/16.49      inference('demod', [status(thm)], ['65', '66'])).
% 16.29/16.49  thf('96', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X1 @ X0))
% 16.29/16.49           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 16.29/16.49      inference('sup+', [status(thm)], ['94', '95'])).
% 16.29/16.49  thf('97', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.29/16.49      inference('sup+', [status(thm)], ['83', '84'])).
% 16.29/16.49  thf(t17_xboole_1, axiom,
% 16.29/16.49    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 16.29/16.49  thf('98', plain,
% 16.29/16.49      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 16.29/16.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 16.29/16.49  thf(t3_xboole_1, axiom,
% 16.29/16.49    (![A:$i]:
% 16.29/16.49     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 16.29/16.49  thf('99', plain,
% 16.29/16.49      (![X23 : $i]:
% 16.29/16.49         (((X23) = (k1_xboole_0)) | ~ (r1_tarski @ X23 @ k1_xboole_0))),
% 16.29/16.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 16.29/16.49  thf('100', plain,
% 16.29/16.49      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 16.29/16.49      inference('sup-', [status(thm)], ['98', '99'])).
% 16.29/16.49  thf('101', plain,
% 16.29/16.49      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 16.29/16.49      inference('sup+', [status(thm)], ['97', '100'])).
% 16.29/16.49  thf('102', plain,
% 16.29/16.49      (![X10 : $i, X11 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X10 @ X11)
% 16.29/16.49           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 16.29/16.49      inference('demod', [status(thm)], ['65', '66'])).
% 16.29/16.49  thf('103', plain,
% 16.29/16.49      (![X0 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 16.29/16.49      inference('sup+', [status(thm)], ['101', '102'])).
% 16.29/16.49  thf('104', plain, (![X22 : $i]: ((k6_subset_1 @ X22 @ k1_xboole_0) = (X22))),
% 16.29/16.49      inference('demod', [status(thm)], ['91', '92'])).
% 16.29/16.49  thf('105', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 16.29/16.49      inference('sup+', [status(thm)], ['103', '104'])).
% 16.29/16.49  thf('106', plain,
% 16.29/16.49      (![X0 : $i, X1 : $i]:
% 16.29/16.49         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X1 @ X0)) = (X0))),
% 16.29/16.49      inference('demod', [status(thm)], ['96', '105'])).
% 16.29/16.49  thf('107', plain,
% 16.29/16.49      ((((k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 16.29/16.49         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.29/16.49      inference('sup+', [status(thm)], ['63', '106'])).
% 16.29/16.49  thf('108', plain,
% 16.29/16.49      (((k1_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.29/16.49      inference('demod', [status(thm)], ['19', '24'])).
% 16.29/16.49  thf('109', plain,
% 16.29/16.49      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 16.29/16.49         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.29/16.49      inference('sup+', [status(thm)], ['107', '108'])).
% 16.29/16.49  thf('110', plain,
% 16.29/16.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf(fc9_tops_1, axiom,
% 16.29/16.49    (![A:$i,B:$i]:
% 16.29/16.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 16.29/16.49         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.29/16.49       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 16.29/16.49  thf('111', plain,
% 16.29/16.49      (![X75 : $i, X76 : $i]:
% 16.29/16.49         (~ (l1_pre_topc @ X75)
% 16.29/16.49          | ~ (v2_pre_topc @ X75)
% 16.29/16.49          | ~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (u1_struct_0 @ X75)))
% 16.29/16.49          | (v3_pre_topc @ (k1_tops_1 @ X75 @ X76) @ X75))),
% 16.29/16.49      inference('cnf', [status(esa)], [fc9_tops_1])).
% 16.29/16.49  thf('112', plain,
% 16.29/16.49      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 16.29/16.49        | ~ (v2_pre_topc @ sk_A)
% 16.29/16.49        | ~ (l1_pre_topc @ sk_A))),
% 16.29/16.49      inference('sup-', [status(thm)], ['110', '111'])).
% 16.29/16.49  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 16.29/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.29/16.49  thf('115', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 16.29/16.49      inference('demod', [status(thm)], ['112', '113', '114'])).
% 16.29/16.49  thf('116', plain,
% 16.29/16.49      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 16.29/16.49         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.29/16.49      inference('sup+', [status(thm)], ['109', '115'])).
% 16.29/16.49  thf('117', plain,
% 16.29/16.49      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.29/16.49      inference('split', [status(esa)], ['0'])).
% 16.29/16.49  thf('118', plain,
% 16.29/16.49      (~
% 16.29/16.49       (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.29/16.49          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.29/16.49             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 16.29/16.49       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.29/16.49      inference('sup-', [status(thm)], ['116', '117'])).
% 16.29/16.49  thf('119', plain, ($false),
% 16.29/16.49      inference('sat_resolution*', [status(thm)], ['1', '43', '44', '118'])).
% 16.29/16.49  
% 16.29/16.49  % SZS output end Refutation
% 16.29/16.49  
% 16.29/16.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
