%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h3x38dN7yJ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:26 EST 2020

% Result     : Theorem 16.25s
% Output     : Refutation 16.25s
% Verified   : 
% Statistics : Number of formulae       :  309 (2076 expanded)
%              Number of leaves         :   51 ( 688 expanded)
%              Depth                    :   26
%              Number of atoms          : 2668 (18200 expanded)
%              Number of equality atoms :  190 (1413 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ~ ( v3_pre_topc @ X61 @ X62 )
      | ~ ( r1_tarski @ X61 @ X63 )
      | ( r1_tarski @ X61 @ ( k1_tops_1 @ X62 @ X63 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ~ ( l1_pre_topc @ X62 ) ) ),
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
    ! [X68: $i,X69: $i] :
      ( ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X69 ) ) )
      | ( ( k1_tops_1 @ X69 @ X68 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X69 ) @ X68 @ ( k2_tops_1 @ X69 @ X68 ) ) )
      | ~ ( l1_pre_topc @ X69 ) ) ),
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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k6_subset_1 @ X44 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k6_subset_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      | ( X0
        = ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k2_tops_1 @ X60 @ X59 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X60 ) @ ( k2_pre_topc @ X60 @ X59 ) @ ( k1_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( l1_pre_topc @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X55 @ X56 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('50',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('56',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('63',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k6_subset_1 @ X12 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('66',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('67',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k6_subset_1 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('70',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('72',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k6_subset_1 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('79',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k6_subset_1 @ X12 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','81'])).

thf('83',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k6_subset_1 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('84',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('86',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('87',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('88',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k6_subset_1 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('94',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('95',plain,(
    ! [X52: $i,X54: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('99',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['92','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('104',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ( ( k2_pre_topc @ X67 @ X66 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X67 ) @ X66 @ ( k2_tops_1 @ X67 @ X66 ) ) )
      | ~ ( l1_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','91'])).

thf('109',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['102','107','108'])).

thf('110',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('111',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('113',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('114',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    ! [X52: $i,X54: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('119',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('120',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('121',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('123',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('124',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('125',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('129',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X29 @ X28 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('134',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k2_tops_1 @ X60 @ X59 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X60 ) @ ( k2_pre_topc @ X60 @ X59 ) @ ( k1_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('141',plain,(
    ! [X52: $i,X54: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('142',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('144',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('148',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_subset_1 @ X0 @ X0 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('152',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('153',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X29 @ X28 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['151','154'])).

thf('156',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('157',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_subset_1 @ X0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['150','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['150','157'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['150','157'])).

thf('161',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('163',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('165',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k6_subset_1 @ X44 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['139','158','159','160','167'])).

thf('169',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['126','168'])).

thf('170',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['121','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('172',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('173',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('175',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','96'])).

thf('178',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('180',plain,(
    ! [X31: $i,X32: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('181',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['176','179','182'])).

thf('184',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X9 @ X10 ) @ X9 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('185',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('186',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('190',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['188','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['183','192'])).

thf('194',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k6_subset_1 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('195',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('196',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['194','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['193','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('204',plain,(
    ! [X5: $i] :
      ( ( k2_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['201','202','205'])).

thf('207',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k6_subset_1 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k6_subset_1 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['176','179','182'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['211','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['210','215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['183','192'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['194','199'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['217','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['216','226'])).

thf('228',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['173','227'])).

thf('229',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['102','107','108'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('231',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('234',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['232','235','236'])).

thf('238',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['188','191'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['237','238'])).

thf('240',plain,
    ( ( k6_subset_1 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['229','239'])).

thf('241',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['194','199'])).

thf('242',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('244',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['228','244'])).

thf('246',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['170','245'])).

thf('247',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('248',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( l1_pre_topc @ X57 )
      | ~ ( v2_pre_topc @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X57 @ X58 ) @ X57 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('249',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['249','250','251'])).

thf('253',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['246','252'])).

thf('254',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('255',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','255'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.h3x38dN7yJ
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 16.25/16.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 16.25/16.41  % Solved by: fo/fo7.sh
% 16.25/16.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.25/16.41  % done 27456 iterations in 15.953s
% 16.25/16.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 16.25/16.41  % SZS output start Refutation
% 16.25/16.41  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 16.25/16.41  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 16.25/16.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 16.25/16.41  thf(sk_B_1_type, type, sk_B_1: $i).
% 16.25/16.41  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 16.25/16.41  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 16.25/16.41  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 16.25/16.41  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 16.25/16.41  thf(sk_A_type, type, sk_A: $i).
% 16.25/16.41  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 16.25/16.41  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 16.25/16.41  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 16.25/16.41  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 16.25/16.41  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 16.25/16.41  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 16.25/16.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 16.25/16.41  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 16.25/16.41  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 16.25/16.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 16.25/16.41  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 16.25/16.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 16.25/16.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 16.25/16.41  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 16.25/16.41  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 16.25/16.41  thf(t76_tops_1, conjecture,
% 16.25/16.41    (![A:$i]:
% 16.25/16.41     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.25/16.41       ( ![B:$i]:
% 16.25/16.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.25/16.41           ( ( v3_pre_topc @ B @ A ) <=>
% 16.25/16.41             ( ( k2_tops_1 @ A @ B ) =
% 16.25/16.41               ( k7_subset_1 @
% 16.25/16.41                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 16.25/16.41  thf(zf_stmt_0, negated_conjecture,
% 16.25/16.41    (~( ![A:$i]:
% 16.25/16.41        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 16.25/16.41          ( ![B:$i]:
% 16.25/16.41            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.25/16.41              ( ( v3_pre_topc @ B @ A ) <=>
% 16.25/16.41                ( ( k2_tops_1 @ A @ B ) =
% 16.25/16.41                  ( k7_subset_1 @
% 16.25/16.41                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 16.25/16.41    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 16.25/16.41  thf('0', plain,
% 16.25/16.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 16.25/16.41        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('1', plain,
% 16.25/16.41      (~
% 16.25/16.41       (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 16.25/16.41       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.25/16.41      inference('split', [status(esa)], ['0'])).
% 16.25/16.41  thf('2', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('3', plain,
% 16.25/16.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 16.25/16.41        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('4', plain,
% 16.25/16.41      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.25/16.41      inference('split', [status(esa)], ['3'])).
% 16.25/16.41  thf('5', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf(t56_tops_1, axiom,
% 16.25/16.41    (![A:$i]:
% 16.25/16.41     ( ( l1_pre_topc @ A ) =>
% 16.25/16.41       ( ![B:$i]:
% 16.25/16.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.25/16.41           ( ![C:$i]:
% 16.25/16.41             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.25/16.41               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 16.25/16.41                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 16.25/16.41  thf('6', plain,
% 16.25/16.41      (![X61 : $i, X62 : $i, X63 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 16.25/16.41          | ~ (v3_pre_topc @ X61 @ X62)
% 16.25/16.41          | ~ (r1_tarski @ X61 @ X63)
% 16.25/16.41          | (r1_tarski @ X61 @ (k1_tops_1 @ X62 @ X63))
% 16.25/16.41          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 16.25/16.41          | ~ (l1_pre_topc @ X62))),
% 16.25/16.41      inference('cnf', [status(esa)], [t56_tops_1])).
% 16.25/16.41  thf('7', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         (~ (l1_pre_topc @ sk_A)
% 16.25/16.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.25/16.41          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 16.25/16.41          | ~ (r1_tarski @ sk_B_1 @ X0)
% 16.25/16.41          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.25/16.41      inference('sup-', [status(thm)], ['5', '6'])).
% 16.25/16.41  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('9', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.25/16.41          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 16.25/16.41          | ~ (r1_tarski @ sk_B_1 @ X0)
% 16.25/16.41          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.25/16.41      inference('demod', [status(thm)], ['7', '8'])).
% 16.25/16.41  thf('10', plain,
% 16.25/16.41      ((![X0 : $i]:
% 16.25/16.41          (~ (r1_tarski @ sk_B_1 @ X0)
% 16.25/16.41           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 16.25/16.41           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 16.25/16.41         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['4', '9'])).
% 16.25/16.41  thf('11', plain,
% 16.25/16.41      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 16.25/16.41         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 16.25/16.41         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['2', '10'])).
% 16.25/16.41  thf(d10_xboole_0, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 16.25/16.41  thf('12', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 16.25/16.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.25/16.41  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 16.25/16.41      inference('simplify', [status(thm)], ['12'])).
% 16.25/16.41  thf('14', plain,
% 16.25/16.41      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 16.25/16.41         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.25/16.41      inference('demod', [status(thm)], ['11', '13'])).
% 16.25/16.41  thf('15', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf(t74_tops_1, axiom,
% 16.25/16.41    (![A:$i]:
% 16.25/16.41     ( ( l1_pre_topc @ A ) =>
% 16.25/16.41       ( ![B:$i]:
% 16.25/16.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.25/16.41           ( ( k1_tops_1 @ A @ B ) =
% 16.25/16.41             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 16.25/16.41  thf('16', plain,
% 16.25/16.41      (![X68 : $i, X69 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X69)))
% 16.25/16.41          | ((k1_tops_1 @ X69 @ X68)
% 16.25/16.41              = (k7_subset_1 @ (u1_struct_0 @ X69) @ X68 @ 
% 16.25/16.41                 (k2_tops_1 @ X69 @ X68)))
% 16.25/16.41          | ~ (l1_pre_topc @ X69))),
% 16.25/16.41      inference('cnf', [status(esa)], [t74_tops_1])).
% 16.25/16.41  thf('17', plain,
% 16.25/16.41      ((~ (l1_pre_topc @ sk_A)
% 16.25/16.41        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.25/16.41               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 16.25/16.41      inference('sup-', [status(thm)], ['15', '16'])).
% 16.25/16.41  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('19', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf(redefinition_k7_subset_1, axiom,
% 16.25/16.41    (![A:$i,B:$i,C:$i]:
% 16.25/16.41     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 16.25/16.41       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 16.25/16.41  thf('20', plain,
% 16.25/16.41      (![X44 : $i, X45 : $i, X46 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 16.25/16.41          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 16.25/16.41      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 16.25/16.41  thf(redefinition_k6_subset_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 16.25/16.41  thf('21', plain,
% 16.25/16.41      (![X42 : $i, X43 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 16.25/16.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.25/16.41  thf('22', plain,
% 16.25/16.41      (![X44 : $i, X45 : $i, X46 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 16.25/16.41          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k6_subset_1 @ X44 @ X46)))),
% 16.25/16.41      inference('demod', [status(thm)], ['20', '21'])).
% 16.25/16.41  thf('23', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 16.25/16.41           = (k6_subset_1 @ sk_B_1 @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['19', '22'])).
% 16.25/16.41  thf('24', plain,
% 16.25/16.41      (((k1_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('demod', [status(thm)], ['17', '18', '23'])).
% 16.25/16.41  thf(t36_xboole_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 16.25/16.41  thf('25', plain,
% 16.25/16.41      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 16.25/16.41      inference('cnf', [status(esa)], [t36_xboole_1])).
% 16.25/16.41  thf('26', plain,
% 16.25/16.41      (![X42 : $i, X43 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 16.25/16.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.25/16.41  thf('27', plain,
% 16.25/16.41      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 16.25/16.41      inference('demod', [status(thm)], ['25', '26'])).
% 16.25/16.41  thf('28', plain,
% 16.25/16.41      (![X0 : $i, X2 : $i]:
% 16.25/16.41         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 16.25/16.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.25/16.41  thf('29', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 16.25/16.41          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['27', '28'])).
% 16.25/16.41  thf('30', plain,
% 16.25/16.41      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 16.25/16.41        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 16.25/16.41      inference('sup-', [status(thm)], ['24', '29'])).
% 16.25/16.41  thf('31', plain,
% 16.25/16.41      (((k1_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('demod', [status(thm)], ['17', '18', '23'])).
% 16.25/16.41  thf('32', plain,
% 16.25/16.41      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 16.25/16.41        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('demod', [status(thm)], ['30', '31'])).
% 16.25/16.41  thf('33', plain,
% 16.25/16.41      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 16.25/16.41         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['14', '32'])).
% 16.25/16.41  thf('34', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf(l78_tops_1, axiom,
% 16.25/16.41    (![A:$i]:
% 16.25/16.41     ( ( l1_pre_topc @ A ) =>
% 16.25/16.41       ( ![B:$i]:
% 16.25/16.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.25/16.41           ( ( k2_tops_1 @ A @ B ) =
% 16.25/16.41             ( k7_subset_1 @
% 16.25/16.41               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 16.25/16.41               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 16.25/16.41  thf('35', plain,
% 16.25/16.41      (![X59 : $i, X60 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 16.25/16.41          | ((k2_tops_1 @ X60 @ X59)
% 16.25/16.41              = (k7_subset_1 @ (u1_struct_0 @ X60) @ 
% 16.25/16.41                 (k2_pre_topc @ X60 @ X59) @ (k1_tops_1 @ X60 @ X59)))
% 16.25/16.41          | ~ (l1_pre_topc @ X60))),
% 16.25/16.41      inference('cnf', [status(esa)], [l78_tops_1])).
% 16.25/16.41  thf('36', plain,
% 16.25/16.41      ((~ (l1_pre_topc @ sk_A)
% 16.25/16.41        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 16.25/16.41      inference('sup-', [status(thm)], ['34', '35'])).
% 16.25/16.41  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('38', plain,
% 16.25/16.41      (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('demod', [status(thm)], ['36', '37'])).
% 16.25/16.41  thf('39', plain,
% 16.25/16.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 16.25/16.41         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.25/16.41      inference('sup+', [status(thm)], ['33', '38'])).
% 16.25/16.41  thf('40', plain,
% 16.25/16.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 16.25/16.41         <= (~
% 16.25/16.41             (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.25/16.41      inference('split', [status(esa)], ['0'])).
% 16.25/16.41  thf('41', plain,
% 16.25/16.41      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 16.25/16.41         <= (~
% 16.25/16.41             (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 16.25/16.41             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['39', '40'])).
% 16.25/16.41  thf('42', plain,
% 16.25/16.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 16.25/16.41       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.25/16.41      inference('simplify', [status(thm)], ['41'])).
% 16.25/16.41  thf('43', plain,
% 16.25/16.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 16.25/16.41       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.25/16.41      inference('split', [status(esa)], ['3'])).
% 16.25/16.41  thf(t7_xboole_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 16.25/16.41  thf('44', plain,
% 16.25/16.41      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 16.25/16.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 16.25/16.41  thf('45', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf(dt_k2_tops_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( ( ( l1_pre_topc @ A ) & 
% 16.25/16.41         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.25/16.41       ( m1_subset_1 @
% 16.25/16.41         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 16.25/16.41  thf('46', plain,
% 16.25/16.41      (![X55 : $i, X56 : $i]:
% 16.25/16.41         (~ (l1_pre_topc @ X55)
% 16.25/16.41          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 16.25/16.41          | (m1_subset_1 @ (k2_tops_1 @ X55 @ X56) @ 
% 16.25/16.41             (k1_zfmisc_1 @ (u1_struct_0 @ X55))))),
% 16.25/16.41      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 16.25/16.41  thf('47', plain,
% 16.25/16.41      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 16.25/16.41         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.25/16.41        | ~ (l1_pre_topc @ sk_A))),
% 16.25/16.41      inference('sup-', [status(thm)], ['45', '46'])).
% 16.25/16.41  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('49', plain,
% 16.25/16.41      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 16.25/16.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('demod', [status(thm)], ['47', '48'])).
% 16.25/16.41  thf(t3_subset, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 16.25/16.41  thf('50', plain,
% 16.25/16.41      (![X52 : $i, X53 : $i]:
% 16.25/16.41         ((r1_tarski @ X52 @ X53) | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53)))),
% 16.25/16.41      inference('cnf', [status(esa)], [t3_subset])).
% 16.25/16.41  thf('51', plain,
% 16.25/16.41      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 16.25/16.41      inference('sup-', [status(thm)], ['49', '50'])).
% 16.25/16.41  thf(t1_xboole_1, axiom,
% 16.25/16.41    (![A:$i,B:$i,C:$i]:
% 16.25/16.41     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 16.25/16.41       ( r1_tarski @ A @ C ) ))).
% 16.25/16.41  thf('52', plain,
% 16.25/16.41      (![X6 : $i, X7 : $i, X8 : $i]:
% 16.25/16.41         (~ (r1_tarski @ X6 @ X7)
% 16.25/16.41          | ~ (r1_tarski @ X7 @ X8)
% 16.25/16.41          | (r1_tarski @ X6 @ X8))),
% 16.25/16.41      inference('cnf', [status(esa)], [t1_xboole_1])).
% 16.25/16.41  thf('53', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ X0)
% 16.25/16.41          | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['51', '52'])).
% 16.25/16.41  thf('54', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 16.25/16.41          (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['44', '53'])).
% 16.25/16.41  thf(t43_xboole_1, axiom,
% 16.25/16.41    (![A:$i,B:$i,C:$i]:
% 16.25/16.41     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 16.25/16.41       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 16.25/16.41  thf('55', plain,
% 16.25/16.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 16.25/16.41         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 16.25/16.41          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 16.25/16.41      inference('cnf', [status(esa)], [t43_xboole_1])).
% 16.25/16.41  thf('56', plain,
% 16.25/16.41      (![X42 : $i, X43 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 16.25/16.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.25/16.41  thf('57', plain,
% 16.25/16.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 16.25/16.41         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 16.25/16.41          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 16.25/16.41      inference('demod', [status(thm)], ['55', '56'])).
% 16.25/16.41  thf('58', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         (r1_tarski @ 
% 16.25/16.41          (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)) @ 
% 16.25/16.41          X0)),
% 16.25/16.41      inference('sup-', [status(thm)], ['54', '57'])).
% 16.25/16.41  thf('59', plain,
% 16.25/16.41      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 16.25/16.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 16.25/16.41  thf('60', plain,
% 16.25/16.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 16.25/16.41         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 16.25/16.41          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 16.25/16.41      inference('demod', [status(thm)], ['55', '56'])).
% 16.25/16.41  thf('61', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 16.25/16.41      inference('sup-', [status(thm)], ['59', '60'])).
% 16.25/16.41  thf(t38_xboole_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 16.25/16.41       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 16.25/16.41  thf('62', plain,
% 16.25/16.41      (![X11 : $i, X12 : $i]:
% 16.25/16.41         (((X11) = (k1_xboole_0))
% 16.25/16.41          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 16.25/16.41      inference('cnf', [status(esa)], [t38_xboole_1])).
% 16.25/16.41  thf('63', plain,
% 16.25/16.41      (![X42 : $i, X43 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 16.25/16.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.25/16.41  thf('64', plain,
% 16.25/16.41      (![X11 : $i, X12 : $i]:
% 16.25/16.41         (((X11) = (k1_xboole_0))
% 16.25/16.41          | ~ (r1_tarski @ X11 @ (k6_subset_1 @ X12 @ X11)))),
% 16.25/16.41      inference('demod', [status(thm)], ['62', '63'])).
% 16.25/16.41  thf('65', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['61', '64'])).
% 16.25/16.41  thf(t51_xboole_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 16.25/16.41       ( A ) ))).
% 16.25/16.41  thf('66', plain,
% 16.25/16.41      (![X16 : $i, X17 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 16.25/16.41           = (X16))),
% 16.25/16.41      inference('cnf', [status(esa)], [t51_xboole_1])).
% 16.25/16.41  thf('67', plain,
% 16.25/16.41      (![X42 : $i, X43 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 16.25/16.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.25/16.41  thf('68', plain,
% 16.25/16.41      (![X16 : $i, X17 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k6_subset_1 @ X16 @ X17))
% 16.25/16.41           = (X16))),
% 16.25/16.41      inference('demod', [status(thm)], ['66', '67'])).
% 16.25/16.41  thf('69', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0) = (X0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['65', '68'])).
% 16.25/16.41  thf(t1_boole, axiom,
% 16.25/16.41    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 16.25/16.41  thf('70', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 16.25/16.41      inference('cnf', [status(esa)], [t1_boole])).
% 16.25/16.41  thf('71', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 16.25/16.41      inference('demod', [status(thm)], ['69', '70'])).
% 16.25/16.41  thf(t100_xboole_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 16.25/16.41  thf('72', plain,
% 16.25/16.41      (![X3 : $i, X4 : $i]:
% 16.25/16.41         ((k4_xboole_0 @ X3 @ X4)
% 16.25/16.41           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 16.25/16.41      inference('cnf', [status(esa)], [t100_xboole_1])).
% 16.25/16.41  thf('73', plain,
% 16.25/16.41      (![X42 : $i, X43 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 16.25/16.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.25/16.41  thf('74', plain,
% 16.25/16.41      (![X3 : $i, X4 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X3 @ X4)
% 16.25/16.41           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 16.25/16.41      inference('demod', [status(thm)], ['72', '73'])).
% 16.25/16.41  thf('75', plain,
% 16.25/16.41      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['71', '74'])).
% 16.25/16.41  thf('76', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['61', '64'])).
% 16.25/16.41  thf('77', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['75', '76'])).
% 16.25/16.41  thf('78', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['61', '64'])).
% 16.25/16.41  thf('79', plain,
% 16.25/16.41      (![X11 : $i, X12 : $i]:
% 16.25/16.41         (((X11) = (k1_xboole_0))
% 16.25/16.41          | ~ (r1_tarski @ X11 @ (k6_subset_1 @ X12 @ X11)))),
% 16.25/16.41      inference('demod', [status(thm)], ['62', '63'])).
% 16.25/16.41  thf('80', plain,
% 16.25/16.41      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['78', '79'])).
% 16.25/16.41  thf('81', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['77', '80'])).
% 16.25/16.41  thf('82', plain,
% 16.25/16.41      (((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 16.25/16.41         = (k1_xboole_0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['58', '81'])).
% 16.25/16.41  thf('83', plain,
% 16.25/16.41      (![X16 : $i, X17 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k6_subset_1 @ X16 @ X17))
% 16.25/16.41           = (X16))),
% 16.25/16.41      inference('demod', [status(thm)], ['66', '67'])).
% 16.25/16.41  thf('84', plain,
% 16.25/16.41      (((k2_xboole_0 @ 
% 16.25/16.41         (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)) @ 
% 16.25/16.41         k1_xboole_0) = (k2_tops_1 @ sk_A @ sk_B_1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['82', '83'])).
% 16.25/16.41  thf('85', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 16.25/16.41      inference('cnf', [status(esa)], [t1_boole])).
% 16.25/16.41  thf('86', plain,
% 16.25/16.41      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 16.25/16.41         = (k2_tops_1 @ sk_A @ sk_B_1))),
% 16.25/16.41      inference('demod', [status(thm)], ['84', '85'])).
% 16.25/16.41  thf(commutativity_k2_tarski, axiom,
% 16.25/16.41    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 16.25/16.41  thf('87', plain,
% 16.25/16.41      (![X20 : $i, X21 : $i]:
% 16.25/16.41         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 16.25/16.41      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 16.25/16.41  thf(t12_setfam_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 16.25/16.41  thf('88', plain,
% 16.25/16.41      (![X50 : $i, X51 : $i]:
% 16.25/16.41         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 16.25/16.41      inference('cnf', [status(esa)], [t12_setfam_1])).
% 16.25/16.41  thf('89', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['87', '88'])).
% 16.25/16.41  thf('90', plain,
% 16.25/16.41      (![X50 : $i, X51 : $i]:
% 16.25/16.41         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 16.25/16.41      inference('cnf', [status(esa)], [t12_setfam_1])).
% 16.25/16.41  thf('91', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['89', '90'])).
% 16.25/16.41  thf('92', plain,
% 16.25/16.41      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))
% 16.25/16.41         = (k2_tops_1 @ sk_A @ sk_B_1))),
% 16.25/16.41      inference('demod', [status(thm)], ['86', '91'])).
% 16.25/16.41  thf('93', plain,
% 16.25/16.41      (![X16 : $i, X17 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k6_subset_1 @ X16 @ X17))
% 16.25/16.41           = (X16))),
% 16.25/16.41      inference('demod', [status(thm)], ['66', '67'])).
% 16.25/16.41  thf('94', plain,
% 16.25/16.41      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 16.25/16.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 16.25/16.41  thf('95', plain,
% 16.25/16.41      (![X52 : $i, X54 : $i]:
% 16.25/16.41         ((m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X52 @ X54))),
% 16.25/16.41      inference('cnf', [status(esa)], [t3_subset])).
% 16.25/16.41  thf('96', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['94', '95'])).
% 16.25/16.41  thf('97', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['93', '96'])).
% 16.25/16.41  thf('98', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf(redefinition_k4_subset_1, axiom,
% 16.25/16.41    (![A:$i,B:$i,C:$i]:
% 16.25/16.41     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 16.25/16.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 16.25/16.41       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 16.25/16.41  thf('99', plain,
% 16.25/16.41      (![X39 : $i, X40 : $i, X41 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 16.25/16.41          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 16.25/16.41          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 16.25/16.41      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 16.25/16.41  thf('100', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 16.25/16.41            = (k2_xboole_0 @ sk_B_1 @ X0))
% 16.25/16.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.25/16.41      inference('sup-', [status(thm)], ['98', '99'])).
% 16.25/16.41  thf('101', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.25/16.41           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 16.25/16.41           = (k2_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['97', '100'])).
% 16.25/16.41  thf('102', plain,
% 16.25/16.41      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.25/16.41         (k2_tops_1 @ sk_A @ sk_B_1))
% 16.25/16.41         = (k2_xboole_0 @ sk_B_1 @ 
% 16.25/16.41            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 16.25/16.41      inference('sup+', [status(thm)], ['92', '101'])).
% 16.25/16.41  thf('103', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf(t65_tops_1, axiom,
% 16.25/16.41    (![A:$i]:
% 16.25/16.41     ( ( l1_pre_topc @ A ) =>
% 16.25/16.41       ( ![B:$i]:
% 16.25/16.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 16.25/16.41           ( ( k2_pre_topc @ A @ B ) =
% 16.25/16.41             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 16.25/16.41  thf('104', plain,
% 16.25/16.41      (![X66 : $i, X67 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 16.25/16.41          | ((k2_pre_topc @ X67 @ X66)
% 16.25/16.41              = (k4_subset_1 @ (u1_struct_0 @ X67) @ X66 @ 
% 16.25/16.41                 (k2_tops_1 @ X67 @ X66)))
% 16.25/16.41          | ~ (l1_pre_topc @ X67))),
% 16.25/16.41      inference('cnf', [status(esa)], [t65_tops_1])).
% 16.25/16.41  thf('105', plain,
% 16.25/16.41      ((~ (l1_pre_topc @ sk_A)
% 16.25/16.41        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 16.25/16.41            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.25/16.41               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 16.25/16.41      inference('sup-', [status(thm)], ['103', '104'])).
% 16.25/16.41  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('107', plain,
% 16.25/16.41      (((k2_pre_topc @ sk_A @ sk_B_1)
% 16.25/16.41         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.25/16.41            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('demod', [status(thm)], ['105', '106'])).
% 16.25/16.41  thf('108', plain,
% 16.25/16.41      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))
% 16.25/16.41         = (k2_tops_1 @ sk_A @ sk_B_1))),
% 16.25/16.41      inference('demod', [status(thm)], ['86', '91'])).
% 16.25/16.41  thf('109', plain,
% 16.25/16.41      (((k2_pre_topc @ sk_A @ sk_B_1)
% 16.25/16.41         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('demod', [status(thm)], ['102', '107', '108'])).
% 16.25/16.41  thf('110', plain,
% 16.25/16.41      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 16.25/16.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 16.25/16.41  thf('111', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['109', '110'])).
% 16.25/16.41  thf('112', plain,
% 16.25/16.41      (((k1_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('demod', [status(thm)], ['17', '18', '23'])).
% 16.25/16.41  thf('113', plain,
% 16.25/16.41      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 16.25/16.41      inference('demod', [status(thm)], ['25', '26'])).
% 16.25/16.41  thf('114', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 16.25/16.41      inference('sup+', [status(thm)], ['112', '113'])).
% 16.25/16.41  thf('115', plain,
% 16.25/16.41      (![X6 : $i, X7 : $i, X8 : $i]:
% 16.25/16.41         (~ (r1_tarski @ X6 @ X7)
% 16.25/16.41          | ~ (r1_tarski @ X7 @ X8)
% 16.25/16.41          | (r1_tarski @ X6 @ X8))),
% 16.25/16.41      inference('cnf', [status(esa)], [t1_xboole_1])).
% 16.25/16.41  thf('116', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0)
% 16.25/16.41          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['114', '115'])).
% 16.25/16.41  thf('117', plain,
% 16.25/16.41      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 16.25/16.41      inference('sup-', [status(thm)], ['111', '116'])).
% 16.25/16.41  thf('118', plain,
% 16.25/16.41      (![X52 : $i, X54 : $i]:
% 16.25/16.41         ((m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X52 @ X54))),
% 16.25/16.41      inference('cnf', [status(esa)], [t3_subset])).
% 16.25/16.41  thf('119', plain,
% 16.25/16.41      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 16.25/16.41        (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['117', '118'])).
% 16.25/16.41  thf(involutiveness_k3_subset_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 16.25/16.41       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 16.25/16.41  thf('120', plain,
% 16.25/16.41      (![X37 : $i, X38 : $i]:
% 16.25/16.41         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 16.25/16.41          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 16.25/16.41      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 16.25/16.41  thf('121', plain,
% 16.25/16.41      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.25/16.41         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.25/16.41          (k1_tops_1 @ sk_A @ sk_B_1)))
% 16.25/16.41         = (k1_tops_1 @ sk_A @ sk_B_1))),
% 16.25/16.41      inference('sup-', [status(thm)], ['119', '120'])).
% 16.25/16.41  thf('122', plain,
% 16.25/16.41      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 16.25/16.41        (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['117', '118'])).
% 16.25/16.41  thf(d5_subset_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 16.25/16.41       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 16.25/16.41  thf('123', plain,
% 16.25/16.41      (![X24 : $i, X25 : $i]:
% 16.25/16.41         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 16.25/16.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 16.25/16.41      inference('cnf', [status(esa)], [d5_subset_1])).
% 16.25/16.41  thf('124', plain,
% 16.25/16.41      (![X42 : $i, X43 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 16.25/16.41      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 16.25/16.41  thf('125', plain,
% 16.25/16.41      (![X24 : $i, X25 : $i]:
% 16.25/16.41         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 16.25/16.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 16.25/16.41      inference('demod', [status(thm)], ['123', '124'])).
% 16.25/16.41  thf('126', plain,
% 16.25/16.41      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.25/16.41         (k1_tops_1 @ sk_A @ sk_B_1))
% 16.25/16.41         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.25/16.41            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['122', '125'])).
% 16.25/16.41  thf('127', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('128', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf(dt_k4_subset_1, axiom,
% 16.25/16.41    (![A:$i,B:$i,C:$i]:
% 16.25/16.41     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 16.25/16.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 16.25/16.41       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 16.25/16.41  thf('129', plain,
% 16.25/16.41      (![X28 : $i, X29 : $i, X30 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 16.25/16.41          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 16.25/16.41          | (m1_subset_1 @ (k4_subset_1 @ X29 @ X28 @ X30) @ 
% 16.25/16.41             (k1_zfmisc_1 @ X29)))),
% 16.25/16.41      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 16.25/16.41  thf('130', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 16.25/16.41           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.25/16.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.25/16.41      inference('sup-', [status(thm)], ['128', '129'])).
% 16.25/16.41  thf('131', plain,
% 16.25/16.41      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_B_1) @ 
% 16.25/16.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['127', '130'])).
% 16.25/16.41  thf('132', plain,
% 16.25/16.41      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('133', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 16.25/16.41            = (k2_xboole_0 @ sk_B_1 @ X0))
% 16.25/16.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.25/16.41      inference('sup-', [status(thm)], ['98', '99'])).
% 16.25/16.41  thf('134', plain,
% 16.25/16.41      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_B_1)
% 16.25/16.41         = (k2_xboole_0 @ sk_B_1 @ sk_B_1))),
% 16.25/16.41      inference('sup-', [status(thm)], ['132', '133'])).
% 16.25/16.41  thf('135', plain,
% 16.25/16.41      ((m1_subset_1 @ (k2_xboole_0 @ sk_B_1 @ sk_B_1) @ 
% 16.25/16.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('demod', [status(thm)], ['131', '134'])).
% 16.25/16.41  thf('136', plain,
% 16.25/16.41      (![X59 : $i, X60 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 16.25/16.41          | ((k2_tops_1 @ X60 @ X59)
% 16.25/16.41              = (k7_subset_1 @ (u1_struct_0 @ X60) @ 
% 16.25/16.41                 (k2_pre_topc @ X60 @ X59) @ (k1_tops_1 @ X60 @ X59)))
% 16.25/16.41          | ~ (l1_pre_topc @ X60))),
% 16.25/16.41      inference('cnf', [status(esa)], [l78_tops_1])).
% 16.25/16.41  thf('137', plain,
% 16.25/16.41      ((~ (l1_pre_topc @ sk_A)
% 16.25/16.41        | ((k2_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_B_1))
% 16.25/16.41            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41               (k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_B_1)) @ 
% 16.25/16.41               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_B_1)))))),
% 16.25/16.41      inference('sup-', [status(thm)], ['135', '136'])).
% 16.25/16.41  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 16.25/16.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.41  thf('139', plain,
% 16.25/16.41      (((k2_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_B_1))
% 16.25/16.41         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41            (k2_pre_topc @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_B_1)) @ 
% 16.25/16.41            (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B_1 @ sk_B_1))))),
% 16.25/16.41      inference('demod', [status(thm)], ['137', '138'])).
% 16.25/16.41  thf('140', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 16.25/16.41      inference('simplify', [status(thm)], ['12'])).
% 16.25/16.41  thf('141', plain,
% 16.25/16.41      (![X52 : $i, X54 : $i]:
% 16.25/16.41         ((m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X52 @ X54))),
% 16.25/16.41      inference('cnf', [status(esa)], [t3_subset])).
% 16.25/16.41  thf('142', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['140', '141'])).
% 16.25/16.41  thf('143', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['140', '141'])).
% 16.25/16.41  thf('144', plain,
% 16.25/16.41      (![X39 : $i, X40 : $i, X41 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 16.25/16.41          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 16.25/16.41          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 16.25/16.41      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 16.25/16.41  thf('145', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 16.25/16.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['143', '144'])).
% 16.25/16.41  thf('146', plain,
% 16.25/16.41      (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['142', '145'])).
% 16.25/16.41  thf('147', plain,
% 16.25/16.41      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 16.25/16.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 16.25/16.41  thf('148', plain,
% 16.25/16.41      (![X0 : $i, X2 : $i]:
% 16.25/16.41         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 16.25/16.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 16.25/16.41  thf('149', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 16.25/16.41          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['147', '148'])).
% 16.25/16.41  thf('150', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         (~ (r1_tarski @ (k4_subset_1 @ X0 @ X0 @ X0) @ X0)
% 16.25/16.41          | ((k2_xboole_0 @ X0 @ X0) = (X0)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['146', '149'])).
% 16.25/16.41  thf('151', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['140', '141'])).
% 16.25/16.41  thf('152', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['140', '141'])).
% 16.25/16.41  thf('153', plain,
% 16.25/16.41      (![X28 : $i, X29 : $i, X30 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 16.25/16.41          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 16.25/16.41          | (m1_subset_1 @ (k4_subset_1 @ X29 @ X28 @ X30) @ 
% 16.25/16.41             (k1_zfmisc_1 @ X29)))),
% 16.25/16.41      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 16.25/16.41  thf('154', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 16.25/16.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['152', '153'])).
% 16.25/16.41  thf('155', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         (m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['151', '154'])).
% 16.25/16.41  thf('156', plain,
% 16.25/16.41      (![X52 : $i, X53 : $i]:
% 16.25/16.41         ((r1_tarski @ X52 @ X53) | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53)))),
% 16.25/16.41      inference('cnf', [status(esa)], [t3_subset])).
% 16.25/16.41  thf('157', plain,
% 16.25/16.41      (![X0 : $i]: (r1_tarski @ (k4_subset_1 @ X0 @ X0 @ X0) @ X0)),
% 16.25/16.41      inference('sup-', [status(thm)], ['155', '156'])).
% 16.25/16.41  thf('158', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 16.25/16.41      inference('demod', [status(thm)], ['150', '157'])).
% 16.25/16.41  thf('159', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 16.25/16.41      inference('demod', [status(thm)], ['150', '157'])).
% 16.25/16.41  thf('160', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 16.25/16.41      inference('demod', [status(thm)], ['150', '157'])).
% 16.25/16.41  thf('161', plain,
% 16.25/16.41      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 16.25/16.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('demod', [status(thm)], ['47', '48'])).
% 16.25/16.41  thf('162', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 16.25/16.41           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 16.25/16.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 16.25/16.41      inference('sup-', [status(thm)], ['128', '129'])).
% 16.25/16.41  thf('163', plain,
% 16.25/16.41      ((m1_subset_1 @ 
% 16.25/16.41        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.25/16.41         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 16.25/16.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['161', '162'])).
% 16.25/16.41  thf('164', plain,
% 16.25/16.41      (((k2_pre_topc @ sk_A @ sk_B_1)
% 16.25/16.41         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 16.25/16.41            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('demod', [status(thm)], ['105', '106'])).
% 16.25/16.41  thf('165', plain,
% 16.25/16.41      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.25/16.41        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.41      inference('demod', [status(thm)], ['163', '164'])).
% 16.25/16.41  thf('166', plain,
% 16.25/16.41      (![X44 : $i, X45 : $i, X46 : $i]:
% 16.25/16.41         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 16.25/16.41          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k6_subset_1 @ X44 @ X46)))),
% 16.25/16.41      inference('demod', [status(thm)], ['20', '21'])).
% 16.25/16.41  thf('167', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 16.25/16.41           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['165', '166'])).
% 16.25/16.41  thf('168', plain,
% 16.25/16.41      (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.25/16.41            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('demod', [status(thm)], ['139', '158', '159', '160', '167'])).
% 16.25/16.41  thf('169', plain,
% 16.25/16.41      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.25/16.41         (k1_tops_1 @ sk_A @ sk_B_1)) = (k2_tops_1 @ sk_A @ sk_B_1))),
% 16.25/16.41      inference('demod', [status(thm)], ['126', '168'])).
% 16.25/16.41  thf('170', plain,
% 16.25/16.41      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.25/16.41         (k2_tops_1 @ sk_A @ sk_B_1)) = (k1_tops_1 @ sk_A @ sk_B_1))),
% 16.25/16.41      inference('demod', [status(thm)], ['121', '169'])).
% 16.25/16.41  thf('171', plain,
% 16.25/16.41      (![X0 : $i]:
% 16.25/16.41         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 16.25/16.41           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['165', '166'])).
% 16.25/16.41  thf('172', plain,
% 16.25/16.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 16.25/16.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.25/16.41      inference('split', [status(esa)], ['3'])).
% 16.25/16.41  thf('173', plain,
% 16.25/16.41      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 16.25/16.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.25/16.41      inference('sup+', [status(thm)], ['171', '172'])).
% 16.25/16.41  thf('174', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['93', '96'])).
% 16.25/16.41  thf('175', plain,
% 16.25/16.41      (![X37 : $i, X38 : $i]:
% 16.25/16.41         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 16.25/16.41          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 16.25/16.41      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 16.25/16.41  thf('176', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 16.25/16.41           = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup-', [status(thm)], ['174', '175'])).
% 16.25/16.41  thf('177', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['93', '96'])).
% 16.25/16.41  thf('178', plain,
% 16.25/16.41      (![X24 : $i, X25 : $i]:
% 16.25/16.41         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 16.25/16.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 16.25/16.41      inference('demod', [status(thm)], ['123', '124'])).
% 16.25/16.41  thf('179', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 16.25/16.41           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['177', '178'])).
% 16.25/16.41  thf(dt_k6_subset_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 16.25/16.41  thf('180', plain,
% 16.25/16.41      (![X31 : $i, X32 : $i]:
% 16.25/16.41         (m1_subset_1 @ (k6_subset_1 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))),
% 16.25/16.41      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 16.25/16.41  thf('181', plain,
% 16.25/16.41      (![X24 : $i, X25 : $i]:
% 16.25/16.41         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 16.25/16.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 16.25/16.41      inference('demod', [status(thm)], ['123', '124'])).
% 16.25/16.41  thf('182', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 16.25/16.41           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['180', '181'])).
% 16.25/16.41  thf('183', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 16.25/16.41           = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('demod', [status(thm)], ['176', '179', '182'])).
% 16.25/16.41  thf('184', plain,
% 16.25/16.41      (![X9 : $i, X10 : $i]: (r1_tarski @ (k6_subset_1 @ X9 @ X10) @ X9)),
% 16.25/16.41      inference('demod', [status(thm)], ['25', '26'])).
% 16.25/16.41  thf('185', plain,
% 16.25/16.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 16.25/16.41         ((r1_tarski @ (k6_subset_1 @ X13 @ X14) @ X15)
% 16.25/16.41          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 16.25/16.41      inference('demod', [status(thm)], ['55', '56'])).
% 16.25/16.41  thf('186', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.25/16.41         (r1_tarski @ 
% 16.25/16.41          (k6_subset_1 @ (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 16.25/16.41          X0)),
% 16.25/16.41      inference('sup-', [status(thm)], ['184', '185'])).
% 16.25/16.41  thf('187', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['77', '80'])).
% 16.25/16.41  thf('188', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.25/16.41         ((k6_subset_1 @ 
% 16.25/16.41           (k6_subset_1 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X2) @ 
% 16.25/16.41           X1) = (k1_xboole_0))),
% 16.25/16.41      inference('sup-', [status(thm)], ['186', '187'])).
% 16.25/16.41  thf('189', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['75', '76'])).
% 16.25/16.41  thf('190', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 16.25/16.41      inference('cnf', [status(esa)], [t1_boole])).
% 16.25/16.41  thf('191', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['189', '190'])).
% 16.25/16.41  thf('192', plain,
% 16.25/16.41      (![X1 : $i, X2 : $i]:
% 16.25/16.41         ((k6_subset_1 @ (k6_subset_1 @ X1 @ X2) @ X1) = (k1_xboole_0))),
% 16.25/16.41      inference('demod', [status(thm)], ['188', '191'])).
% 16.25/16.41  thf('193', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k6_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['183', '192'])).
% 16.25/16.41  thf('194', plain,
% 16.25/16.41      (![X16 : $i, X17 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k6_subset_1 @ X16 @ X17))
% 16.25/16.41           = (X16))),
% 16.25/16.41      inference('demod', [status(thm)], ['66', '67'])).
% 16.25/16.41  thf('195', plain,
% 16.25/16.41      (![X20 : $i, X21 : $i]:
% 16.25/16.41         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 16.25/16.41      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 16.25/16.41  thf(l51_zfmisc_1, axiom,
% 16.25/16.41    (![A:$i,B:$i]:
% 16.25/16.41     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 16.25/16.41  thf('196', plain,
% 16.25/16.41      (![X22 : $i, X23 : $i]:
% 16.25/16.41         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 16.25/16.41      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 16.25/16.41  thf('197', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['195', '196'])).
% 16.25/16.41  thf('198', plain,
% 16.25/16.41      (![X22 : $i, X23 : $i]:
% 16.25/16.41         ((k3_tarski @ (k2_tarski @ X22 @ X23)) = (k2_xboole_0 @ X22 @ X23))),
% 16.25/16.41      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 16.25/16.41  thf('199', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['197', '198'])).
% 16.25/16.41  thf('200', plain,
% 16.25/16.41      (![X16 : $i, X17 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 16.25/16.41           = (X16))),
% 16.25/16.41      inference('demod', [status(thm)], ['194', '199'])).
% 16.25/16.41  thf('201', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ k1_xboole_0 @ 
% 16.25/16.41           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))
% 16.25/16.41           = (k3_xboole_0 @ X1 @ X0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['193', '200'])).
% 16.25/16.41  thf('202', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['89', '90'])).
% 16.25/16.41  thf('203', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['197', '198'])).
% 16.25/16.41  thf('204', plain, (![X5 : $i]: ((k2_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 16.25/16.41      inference('cnf', [status(esa)], [t1_boole])).
% 16.25/16.41  thf('205', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['203', '204'])).
% 16.25/16.41  thf('206', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.25/16.41           = (k3_xboole_0 @ X1 @ X0))),
% 16.25/16.41      inference('demod', [status(thm)], ['201', '202', '205'])).
% 16.25/16.41  thf('207', plain,
% 16.25/16.41      (![X3 : $i, X4 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X3 @ X4)
% 16.25/16.41           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 16.25/16.41      inference('demod', [status(thm)], ['72', '73'])).
% 16.25/16.41  thf('208', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.25/16.41           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.25/16.41      inference('sup+', [status(thm)], ['206', '207'])).
% 16.25/16.41  thf('209', plain,
% 16.25/16.41      (![X3 : $i, X4 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X3 @ X4)
% 16.25/16.41           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 16.25/16.41      inference('demod', [status(thm)], ['72', '73'])).
% 16.25/16.41  thf('210', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.25/16.41           = (k6_subset_1 @ X1 @ X0))),
% 16.25/16.41      inference('demod', [status(thm)], ['208', '209'])).
% 16.25/16.41  thf('211', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 16.25/16.41           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['180', '181'])).
% 16.25/16.41  thf('212', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 16.25/16.41           = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('demod', [status(thm)], ['176', '179', '182'])).
% 16.25/16.41  thf('213', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.25/16.41           = (k6_subset_1 @ X1 @ X0))),
% 16.25/16.41      inference('demod', [status(thm)], ['208', '209'])).
% 16.25/16.41  thf('214', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 16.25/16.41           = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('demod', [status(thm)], ['212', '213'])).
% 16.25/16.41  thf('215', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 16.25/16.41           = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('demod', [status(thm)], ['211', '214'])).
% 16.25/16.41  thf('216', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 16.25/16.41           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 16.25/16.41      inference('sup+', [status(thm)], ['210', '215'])).
% 16.25/16.41  thf('217', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['89', '90'])).
% 16.25/16.41  thf('218', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['89', '90'])).
% 16.25/16.41  thf('219', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k6_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['183', '192'])).
% 16.25/16.41  thf('220', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k6_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['218', '219'])).
% 16.25/16.41  thf('221', plain,
% 16.25/16.41      (![X16 : $i, X17 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 16.25/16.41           = (X16))),
% 16.25/16.41      inference('demod', [status(thm)], ['194', '199'])).
% 16.25/16.41  thf('222', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k2_xboole_0 @ k1_xboole_0 @ 
% 16.25/16.41           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 16.25/16.41           = (k3_xboole_0 @ X1 @ X0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['220', '221'])).
% 16.25/16.41  thf('223', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['89', '90'])).
% 16.25/16.41  thf('224', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 16.25/16.41      inference('sup+', [status(thm)], ['203', '204'])).
% 16.25/16.41  thf('225', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 16.25/16.41           = (k3_xboole_0 @ X1 @ X0))),
% 16.25/16.41      inference('demod', [status(thm)], ['222', '223', '224'])).
% 16.25/16.41  thf('226', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 16.25/16.41           = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('sup+', [status(thm)], ['217', '225'])).
% 16.25/16.41  thf('227', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 16.25/16.41           = (k3_xboole_0 @ X0 @ X1))),
% 16.25/16.41      inference('demod', [status(thm)], ['216', '226'])).
% 16.25/16.41  thf('228', plain,
% 16.25/16.41      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.25/16.41          (k2_tops_1 @ sk_A @ sk_B_1))
% 16.25/16.41          = (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))))
% 16.25/16.41         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.41                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.41                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.25/16.41      inference('sup+', [status(thm)], ['173', '227'])).
% 16.25/16.41  thf('229', plain,
% 16.25/16.41      (((k2_pre_topc @ sk_A @ sk_B_1)
% 16.25/16.41         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 16.25/16.41      inference('demod', [status(thm)], ['102', '107', '108'])).
% 16.25/16.41  thf('230', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['94', '95'])).
% 16.25/16.41  thf('231', plain,
% 16.25/16.41      (![X37 : $i, X38 : $i]:
% 16.25/16.41         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 16.25/16.41          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 16.25/16.41      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 16.25/16.41  thf('232', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 16.25/16.41           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 16.25/16.41      inference('sup-', [status(thm)], ['230', '231'])).
% 16.25/16.41  thf('233', plain,
% 16.25/16.41      (![X0 : $i, X1 : $i]:
% 16.25/16.41         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 16.25/16.41      inference('sup-', [status(thm)], ['94', '95'])).
% 16.25/16.41  thf('234', plain,
% 16.25/16.41      (![X24 : $i, X25 : $i]:
% 16.25/16.41         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 16.25/16.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 16.25/16.41      inference('demod', [status(thm)], ['123', '124'])).
% 16.25/16.42  thf('235', plain,
% 16.25/16.42      (![X0 : $i, X1 : $i]:
% 16.25/16.42         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 16.25/16.42           = (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 16.25/16.42      inference('sup-', [status(thm)], ['233', '234'])).
% 16.25/16.42  thf('236', plain,
% 16.25/16.42      (![X0 : $i, X1 : $i]:
% 16.25/16.42         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 16.25/16.42           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 16.25/16.42      inference('sup-', [status(thm)], ['180', '181'])).
% 16.25/16.42  thf('237', plain,
% 16.25/16.42      (![X0 : $i, X1 : $i]:
% 16.25/16.42         ((k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 16.25/16.42           (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 16.25/16.42      inference('demod', [status(thm)], ['232', '235', '236'])).
% 16.25/16.42  thf('238', plain,
% 16.25/16.42      (![X1 : $i, X2 : $i]:
% 16.25/16.42         ((k6_subset_1 @ (k6_subset_1 @ X1 @ X2) @ X1) = (k1_xboole_0))),
% 16.25/16.42      inference('demod', [status(thm)], ['188', '191'])).
% 16.25/16.42  thf('239', plain,
% 16.25/16.42      (![X0 : $i, X1 : $i]:
% 16.25/16.42         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 16.25/16.42      inference('sup+', [status(thm)], ['237', '238'])).
% 16.25/16.42  thf('240', plain,
% 16.25/16.42      (((k6_subset_1 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 16.25/16.42      inference('sup+', [status(thm)], ['229', '239'])).
% 16.25/16.42  thf('241', plain,
% 16.25/16.42      (![X16 : $i, X17 : $i]:
% 16.25/16.42         ((k2_xboole_0 @ (k6_subset_1 @ X16 @ X17) @ (k3_xboole_0 @ X16 @ X17))
% 16.25/16.42           = (X16))),
% 16.25/16.42      inference('demod', [status(thm)], ['194', '199'])).
% 16.25/16.42  thf('242', plain,
% 16.25/16.42      (((k2_xboole_0 @ k1_xboole_0 @ 
% 16.25/16.42         (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))) = (sk_B_1))),
% 16.25/16.42      inference('sup+', [status(thm)], ['240', '241'])).
% 16.25/16.42  thf('243', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 16.25/16.42      inference('sup+', [status(thm)], ['203', '204'])).
% 16.25/16.42  thf('244', plain,
% 16.25/16.42      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 16.25/16.42      inference('demod', [status(thm)], ['242', '243'])).
% 16.25/16.42  thf('245', plain,
% 16.25/16.42      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 16.25/16.42          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 16.25/16.42         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.42                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.25/16.42      inference('demod', [status(thm)], ['228', '244'])).
% 16.25/16.42  thf('246', plain,
% 16.25/16.42      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 16.25/16.42         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.42                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.25/16.42      inference('sup+', [status(thm)], ['170', '245'])).
% 16.25/16.42  thf('247', plain,
% 16.25/16.42      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 16.25/16.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.42  thf(fc9_tops_1, axiom,
% 16.25/16.42    (![A:$i,B:$i]:
% 16.25/16.42     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 16.25/16.42         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 16.25/16.42       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 16.25/16.42  thf('248', plain,
% 16.25/16.42      (![X57 : $i, X58 : $i]:
% 16.25/16.42         (~ (l1_pre_topc @ X57)
% 16.25/16.42          | ~ (v2_pre_topc @ X57)
% 16.25/16.42          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 16.25/16.42          | (v3_pre_topc @ (k1_tops_1 @ X57 @ X58) @ X57))),
% 16.25/16.42      inference('cnf', [status(esa)], [fc9_tops_1])).
% 16.25/16.42  thf('249', plain,
% 16.25/16.42      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 16.25/16.42        | ~ (v2_pre_topc @ sk_A)
% 16.25/16.42        | ~ (l1_pre_topc @ sk_A))),
% 16.25/16.42      inference('sup-', [status(thm)], ['247', '248'])).
% 16.25/16.42  thf('250', plain, ((v2_pre_topc @ sk_A)),
% 16.25/16.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.42  thf('251', plain, ((l1_pre_topc @ sk_A)),
% 16.25/16.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.25/16.42  thf('252', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 16.25/16.42      inference('demod', [status(thm)], ['249', '250', '251'])).
% 16.25/16.42  thf('253', plain,
% 16.25/16.42      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 16.25/16.42         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.42                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 16.25/16.42      inference('sup+', [status(thm)], ['246', '252'])).
% 16.25/16.42  thf('254', plain,
% 16.25/16.42      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 16.25/16.42      inference('split', [status(esa)], ['0'])).
% 16.25/16.42  thf('255', plain,
% 16.25/16.42      (~
% 16.25/16.42       (((k2_tops_1 @ sk_A @ sk_B_1)
% 16.25/16.42          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 16.25/16.42             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 16.25/16.42       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 16.25/16.42      inference('sup-', [status(thm)], ['253', '254'])).
% 16.25/16.42  thf('256', plain, ($false),
% 16.25/16.42      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '255'])).
% 16.25/16.42  
% 16.25/16.42  % SZS output end Refutation
% 16.25/16.42  
% 16.25/16.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
