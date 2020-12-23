%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PJeAteYcBh

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:23 EST 2020

% Result     : Theorem 29.50s
% Output     : Refutation 29.50s
% Verified   : 
% Statistics : Number of formulae       :  325 (3742 expanded)
%              Number of leaves         :   51 (1261 expanded)
%              Depth                    :   26
%              Number of atoms          : 2886 (30534 expanded)
%              Number of equality atoms :  215 (2650 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

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

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
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

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( l1_pre_topc @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X55 @ X56 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X55 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X29 @ X28 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X66: $i,X67: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ( ( k2_pre_topc @ X67 @ X66 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X67 ) @ X66 @ ( k2_tops_1 @ X67 @ X66 ) ) )
      | ~ ( l1_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k6_subset_1 @ X44 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('63',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('64',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X50: $i,X51: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X50 @ X51 ) )
      = ( k3_xboole_0 @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('69',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['67','71'])).

thf('73',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) )
      = ( k2_pre_topc @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['62','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('75',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('76',plain,(
    ! [X52: $i,X54: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('80',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k7_subset_1 @ X48 @ X49 @ X47 )
        = ( k9_subset_1 @ X48 @ X49 @ ( k3_subset_1 @ X48 @ X47 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X1 )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('83',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('84',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('85',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X1 )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X1 )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('90',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k6_subset_1 @ X44 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ X2 )
      = ( k6_subset_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('94',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('97',plain,(
    ! [X31: $i,X32: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('98',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['95','96','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('102',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('103',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('104',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('107',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('110',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('121',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('122',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k6_subset_1 @ X42 @ X43 )
      = ( k4_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('123',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('131',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','133'])).

thf('135',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('140',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['138','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['92','142'])).

thf('144',plain,
    ( ( ( k6_subset_1 @ ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k9_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['73','143'])).

thf('145',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('147',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('150',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['147','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('153',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('155',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('157',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('158',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','159'])).

thf('161',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('162',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('164',plain,
    ( ( k6_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('166',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('168',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('170',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['153','170'])).

thf('172',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('173',plain,(
    ! [X31: $i,X32: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('174',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['171','176'])).

thf('178',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('179',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['153','170'])).

thf('180',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('182',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('184',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['180','181'])).

thf('185',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['180','181'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('187',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('188',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('189',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','132'])).

thf('190',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X1 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('199',plain,(
    ! [X52: $i,X54: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X54 ) )
      | ~ ( r1_tarski @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('200',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k4_subset_1 @ X40 @ X39 @ X41 )
        = ( k2_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['197','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('205',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('206',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X29 @ X28 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['204','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['203','208'])).

thf('210',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('213',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['211','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['194','215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','133'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['216','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('229',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('232',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k6_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['230','233','234'])).

thf('236',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','132'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['227','237'])).

thf('239',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X18 @ X19 ) @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['230','233','234'])).

thf('245',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['240','241','242'])).

thf('249',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['248','249'])).

thf('251',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['247','252'])).

thf('254',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['194','215'])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['226','253','254'])).

thf('256',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
      = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['188','255'])).

thf('257',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['180','181'])).

thf('258',plain,
    ( ( sk_B_1
      = ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('260',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X35 @ X34 @ X34 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['144','182','183','184','185','186','187','258','261'])).

thf('263',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('264',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( l1_pre_topc @ X57 )
      | ~ ( v2_pre_topc @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X57 @ X58 ) @ X57 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('265',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['262','268'])).

thf('270',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('271',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','271'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PJeAteYcBh
% 0.16/0.36  % Computer   : n003.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:19:57 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 29.50/29.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 29.50/29.79  % Solved by: fo/fo7.sh
% 29.50/29.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.50/29.79  % done 41326 iterations in 29.307s
% 29.50/29.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 29.50/29.79  % SZS output start Refutation
% 29.50/29.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 29.50/29.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 29.50/29.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 29.50/29.79  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 29.50/29.79  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 29.50/29.79  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 29.50/29.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.50/29.79  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 29.50/29.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 29.50/29.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 29.50/29.79  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 29.50/29.79  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 29.50/29.79  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 29.50/29.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 29.50/29.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 29.50/29.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 29.50/29.79  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 29.50/29.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 29.50/29.79  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 29.50/29.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 29.50/29.79  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 29.50/29.79  thf(sk_A_type, type, sk_A: $i).
% 29.50/29.79  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 29.50/29.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 29.50/29.79  thf(t76_tops_1, conjecture,
% 29.50/29.79    (![A:$i]:
% 29.50/29.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.50/29.79       ( ![B:$i]:
% 29.50/29.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.50/29.79           ( ( v3_pre_topc @ B @ A ) <=>
% 29.50/29.79             ( ( k2_tops_1 @ A @ B ) =
% 29.50/29.79               ( k7_subset_1 @
% 29.50/29.79                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 29.50/29.79  thf(zf_stmt_0, negated_conjecture,
% 29.50/29.79    (~( ![A:$i]:
% 29.50/29.79        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 29.50/29.79          ( ![B:$i]:
% 29.50/29.79            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.50/29.79              ( ( v3_pre_topc @ B @ A ) <=>
% 29.50/29.79                ( ( k2_tops_1 @ A @ B ) =
% 29.50/29.79                  ( k7_subset_1 @
% 29.50/29.79                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 29.50/29.79    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 29.50/29.79  thf('0', plain,
% 29.50/29.79      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 29.50/29.79        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf('1', plain,
% 29.50/29.79      (~
% 29.50/29.79       (((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 29.50/29.79       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 29.50/29.79      inference('split', [status(esa)], ['0'])).
% 29.50/29.79  thf('2', plain,
% 29.50/29.79      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf('3', plain,
% 29.50/29.79      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 29.50/29.79        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf('4', plain,
% 29.50/29.79      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 29.50/29.79      inference('split', [status(esa)], ['3'])).
% 29.50/29.79  thf('5', plain,
% 29.50/29.79      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf(t56_tops_1, axiom,
% 29.50/29.79    (![A:$i]:
% 29.50/29.79     ( ( l1_pre_topc @ A ) =>
% 29.50/29.79       ( ![B:$i]:
% 29.50/29.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.50/29.79           ( ![C:$i]:
% 29.50/29.79             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.50/29.79               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 29.50/29.79                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 29.50/29.79  thf('6', plain,
% 29.50/29.79      (![X61 : $i, X62 : $i, X63 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 29.50/29.79          | ~ (v3_pre_topc @ X61 @ X62)
% 29.50/29.79          | ~ (r1_tarski @ X61 @ X63)
% 29.50/29.79          | (r1_tarski @ X61 @ (k1_tops_1 @ X62 @ X63))
% 29.50/29.79          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 29.50/29.79          | ~ (l1_pre_topc @ X62))),
% 29.50/29.79      inference('cnf', [status(esa)], [t56_tops_1])).
% 29.50/29.79  thf('7', plain,
% 29.50/29.79      (![X0 : $i]:
% 29.50/29.79         (~ (l1_pre_topc @ sk_A)
% 29.50/29.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 29.50/29.79          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 29.50/29.79          | ~ (r1_tarski @ sk_B_1 @ X0)
% 29.50/29.79          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 29.50/29.79      inference('sup-', [status(thm)], ['5', '6'])).
% 29.50/29.79  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf('9', plain,
% 29.50/29.79      (![X0 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 29.50/29.79          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 29.50/29.79          | ~ (r1_tarski @ sk_B_1 @ X0)
% 29.50/29.79          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 29.50/29.79      inference('demod', [status(thm)], ['7', '8'])).
% 29.50/29.79  thf('10', plain,
% 29.50/29.79      ((![X0 : $i]:
% 29.50/29.79          (~ (r1_tarski @ sk_B_1 @ X0)
% 29.50/29.79           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 29.50/29.79           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 29.50/29.79         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['4', '9'])).
% 29.50/29.79  thf('11', plain,
% 29.50/29.79      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 29.50/29.79         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 29.50/29.79         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['2', '10'])).
% 29.50/29.79  thf(d10_xboole_0, axiom,
% 29.50/29.79    (![A:$i,B:$i]:
% 29.50/29.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 29.50/29.79  thf('12', plain,
% 29.50/29.79      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 29.50/29.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 29.50/29.79  thf('13', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 29.50/29.79      inference('simplify', [status(thm)], ['12'])).
% 29.50/29.79  thf('14', plain,
% 29.50/29.79      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 29.50/29.79         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 29.50/29.79      inference('demod', [status(thm)], ['11', '13'])).
% 29.50/29.79  thf('15', plain,
% 29.50/29.79      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf(t74_tops_1, axiom,
% 29.50/29.79    (![A:$i]:
% 29.50/29.79     ( ( l1_pre_topc @ A ) =>
% 29.50/29.79       ( ![B:$i]:
% 29.50/29.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.50/29.79           ( ( k1_tops_1 @ A @ B ) =
% 29.50/29.79             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 29.50/29.79  thf('16', plain,
% 29.50/29.79      (![X68 : $i, X69 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X69)))
% 29.50/29.79          | ((k1_tops_1 @ X69 @ X68)
% 29.50/29.79              = (k7_subset_1 @ (u1_struct_0 @ X69) @ X68 @ 
% 29.50/29.79                 (k2_tops_1 @ X69 @ X68)))
% 29.50/29.79          | ~ (l1_pre_topc @ X69))),
% 29.50/29.79      inference('cnf', [status(esa)], [t74_tops_1])).
% 29.50/29.79  thf('17', plain,
% 29.50/29.79      ((~ (l1_pre_topc @ sk_A)
% 29.50/29.79        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 29.50/29.79               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 29.50/29.79      inference('sup-', [status(thm)], ['15', '16'])).
% 29.50/29.79  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf('19', plain,
% 29.50/29.79      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf(redefinition_k7_subset_1, axiom,
% 29.50/29.79    (![A:$i,B:$i,C:$i]:
% 29.50/29.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 29.50/29.79       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 29.50/29.79  thf('20', plain,
% 29.50/29.79      (![X44 : $i, X45 : $i, X46 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 29.50/29.79          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 29.50/29.79      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 29.50/29.79  thf(redefinition_k6_subset_1, axiom,
% 29.50/29.79    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 29.50/29.79  thf('21', plain,
% 29.50/29.79      (![X42 : $i, X43 : $i]:
% 29.50/29.79         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 29.50/29.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 29.50/29.79  thf('22', plain,
% 29.50/29.79      (![X44 : $i, X45 : $i, X46 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 29.50/29.79          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k6_subset_1 @ X44 @ X46)))),
% 29.50/29.79      inference('demod', [status(thm)], ['20', '21'])).
% 29.50/29.79  thf('23', plain,
% 29.50/29.79      (![X0 : $i]:
% 29.50/29.79         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 29.50/29.79           = (k6_subset_1 @ sk_B_1 @ X0))),
% 29.50/29.79      inference('sup-', [status(thm)], ['19', '22'])).
% 29.50/29.79  thf('24', plain,
% 29.50/29.79      (((k1_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.79      inference('demod', [status(thm)], ['17', '18', '23'])).
% 29.50/29.79  thf(dt_k6_subset_1, axiom,
% 29.50/29.79    (![A:$i,B:$i]:
% 29.50/29.79     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 29.50/29.79  thf('25', plain,
% 29.50/29.79      (![X31 : $i, X32 : $i]:
% 29.50/29.79         (m1_subset_1 @ (k6_subset_1 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))),
% 29.50/29.79      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 29.50/29.79  thf(t3_subset, axiom,
% 29.50/29.79    (![A:$i,B:$i]:
% 29.50/29.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 29.50/29.79  thf('26', plain,
% 29.50/29.79      (![X52 : $i, X53 : $i]:
% 29.50/29.79         ((r1_tarski @ X52 @ X53) | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53)))),
% 29.50/29.79      inference('cnf', [status(esa)], [t3_subset])).
% 29.50/29.79  thf('27', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 29.50/29.79      inference('sup-', [status(thm)], ['25', '26'])).
% 29.50/29.79  thf('28', plain,
% 29.50/29.79      (![X2 : $i, X4 : $i]:
% 29.50/29.79         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 29.50/29.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 29.50/29.79  thf('29', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 29.50/29.79          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['27', '28'])).
% 29.50/29.79  thf('30', plain,
% 29.50/29.79      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 29.50/29.79        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 29.50/29.79      inference('sup-', [status(thm)], ['24', '29'])).
% 29.50/29.79  thf('31', plain,
% 29.50/29.79      (((k1_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.79      inference('demod', [status(thm)], ['17', '18', '23'])).
% 29.50/29.79  thf('32', plain,
% 29.50/29.79      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 29.50/29.79        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.79      inference('demod', [status(thm)], ['30', '31'])).
% 29.50/29.79  thf('33', plain,
% 29.50/29.79      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 29.50/29.79         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['14', '32'])).
% 29.50/29.79  thf('34', plain,
% 29.50/29.79      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf(l78_tops_1, axiom,
% 29.50/29.79    (![A:$i]:
% 29.50/29.79     ( ( l1_pre_topc @ A ) =>
% 29.50/29.79       ( ![B:$i]:
% 29.50/29.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.50/29.79           ( ( k2_tops_1 @ A @ B ) =
% 29.50/29.79             ( k7_subset_1 @
% 29.50/29.79               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 29.50/29.79               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 29.50/29.79  thf('35', plain,
% 29.50/29.79      (![X59 : $i, X60 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 29.50/29.79          | ((k2_tops_1 @ X60 @ X59)
% 29.50/29.79              = (k7_subset_1 @ (u1_struct_0 @ X60) @ 
% 29.50/29.79                 (k2_pre_topc @ X60 @ X59) @ (k1_tops_1 @ X60 @ X59)))
% 29.50/29.79          | ~ (l1_pre_topc @ X60))),
% 29.50/29.79      inference('cnf', [status(esa)], [l78_tops_1])).
% 29.50/29.79  thf('36', plain,
% 29.50/29.79      ((~ (l1_pre_topc @ sk_A)
% 29.50/29.79        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 29.50/29.79      inference('sup-', [status(thm)], ['34', '35'])).
% 29.50/29.79  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf('38', plain,
% 29.50/29.79      (((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.79      inference('demod', [status(thm)], ['36', '37'])).
% 29.50/29.79  thf('39', plain,
% 29.50/29.79      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 29.50/29.79         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 29.50/29.79      inference('sup+', [status(thm)], ['33', '38'])).
% 29.50/29.79  thf('40', plain,
% 29.50/29.79      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 29.50/29.79         <= (~
% 29.50/29.79             (((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 29.50/29.79      inference('split', [status(esa)], ['0'])).
% 29.50/29.79  thf('41', plain,
% 29.50/29.79      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 29.50/29.79         <= (~
% 29.50/29.79             (((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 29.50/29.79             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['39', '40'])).
% 29.50/29.79  thf('42', plain,
% 29.50/29.79      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 29.50/29.79       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 29.50/29.79      inference('simplify', [status(thm)], ['41'])).
% 29.50/29.79  thf('43', plain,
% 29.50/29.79      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 29.50/29.79       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 29.50/29.79      inference('split', [status(esa)], ['3'])).
% 29.50/29.79  thf('44', plain,
% 29.50/29.79      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf(dt_k2_tops_1, axiom,
% 29.50/29.79    (![A:$i,B:$i]:
% 29.50/29.79     ( ( ( l1_pre_topc @ A ) & 
% 29.50/29.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 29.50/29.79       ( m1_subset_1 @
% 29.50/29.79         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 29.50/29.79  thf('45', plain,
% 29.50/29.79      (![X55 : $i, X56 : $i]:
% 29.50/29.79         (~ (l1_pre_topc @ X55)
% 29.50/29.79          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X55)))
% 29.50/29.79          | (m1_subset_1 @ (k2_tops_1 @ X55 @ X56) @ 
% 29.50/29.79             (k1_zfmisc_1 @ (u1_struct_0 @ X55))))),
% 29.50/29.79      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 29.50/29.79  thf('46', plain,
% 29.50/29.79      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 29.50/29.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 29.50/29.79        | ~ (l1_pre_topc @ sk_A))),
% 29.50/29.79      inference('sup-', [status(thm)], ['44', '45'])).
% 29.50/29.79  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf('48', plain,
% 29.50/29.79      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 29.50/29.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('demod', [status(thm)], ['46', '47'])).
% 29.50/29.79  thf('49', plain,
% 29.50/29.79      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf(dt_k4_subset_1, axiom,
% 29.50/29.79    (![A:$i,B:$i,C:$i]:
% 29.50/29.79     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 29.50/29.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 29.50/29.79       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 29.50/29.79  thf('50', plain,
% 29.50/29.79      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 29.50/29.79          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 29.50/29.79          | (m1_subset_1 @ (k4_subset_1 @ X29 @ X28 @ X30) @ 
% 29.50/29.79             (k1_zfmisc_1 @ X29)))),
% 29.50/29.79      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 29.50/29.79  thf('51', plain,
% 29.50/29.79      (![X0 : $i]:
% 29.50/29.79         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 29.50/29.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 29.50/29.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 29.50/29.79      inference('sup-', [status(thm)], ['49', '50'])).
% 29.50/29.79  thf('52', plain,
% 29.50/29.79      ((m1_subset_1 @ 
% 29.50/29.79        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 29.50/29.79         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 29.50/29.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['48', '51'])).
% 29.50/29.79  thf('53', plain,
% 29.50/29.79      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf(t65_tops_1, axiom,
% 29.50/29.79    (![A:$i]:
% 29.50/29.79     ( ( l1_pre_topc @ A ) =>
% 29.50/29.79       ( ![B:$i]:
% 29.50/29.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 29.50/29.79           ( ( k2_pre_topc @ A @ B ) =
% 29.50/29.79             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 29.50/29.79  thf('54', plain,
% 29.50/29.79      (![X66 : $i, X67 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 29.50/29.79          | ((k2_pre_topc @ X67 @ X66)
% 29.50/29.79              = (k4_subset_1 @ (u1_struct_0 @ X67) @ X66 @ 
% 29.50/29.79                 (k2_tops_1 @ X67 @ X66)))
% 29.50/29.79          | ~ (l1_pre_topc @ X67))),
% 29.50/29.79      inference('cnf', [status(esa)], [t65_tops_1])).
% 29.50/29.79  thf('55', plain,
% 29.50/29.79      ((~ (l1_pre_topc @ sk_A)
% 29.50/29.79        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 29.50/29.79            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 29.50/29.79               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 29.50/29.79      inference('sup-', [status(thm)], ['53', '54'])).
% 29.50/29.79  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 29.50/29.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.79  thf('57', plain,
% 29.50/29.79      (((k2_pre_topc @ sk_A @ sk_B_1)
% 29.50/29.79         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 29.50/29.79            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.79      inference('demod', [status(thm)], ['55', '56'])).
% 29.50/29.79  thf('58', plain,
% 29.50/29.79      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 29.50/29.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.79      inference('demod', [status(thm)], ['52', '57'])).
% 29.50/29.79  thf('59', plain,
% 29.50/29.79      (![X44 : $i, X45 : $i, X46 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 29.50/29.79          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k6_subset_1 @ X44 @ X46)))),
% 29.50/29.79      inference('demod', [status(thm)], ['20', '21'])).
% 29.50/29.79  thf('60', plain,
% 29.50/29.79      (![X0 : $i]:
% 29.50/29.79         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 29.50/29.79           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 29.50/29.79      inference('sup-', [status(thm)], ['58', '59'])).
% 29.50/29.79  thf('61', plain,
% 29.50/29.79      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 29.50/29.79         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 29.50/29.79      inference('split', [status(esa)], ['3'])).
% 29.50/29.79  thf('62', plain,
% 29.50/29.79      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 29.50/29.79         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 29.50/29.79      inference('sup+', [status(thm)], ['60', '61'])).
% 29.50/29.79  thf(commutativity_k2_tarski, axiom,
% 29.50/29.79    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 29.50/29.79  thf('63', plain,
% 29.50/29.79      (![X22 : $i, X23 : $i]:
% 29.50/29.79         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 29.50/29.79      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 29.50/29.79  thf(t12_setfam_1, axiom,
% 29.50/29.79    (![A:$i,B:$i]:
% 29.50/29.79     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 29.50/29.79  thf('64', plain,
% 29.50/29.79      (![X50 : $i, X51 : $i]:
% 29.50/29.79         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 29.50/29.79      inference('cnf', [status(esa)], [t12_setfam_1])).
% 29.50/29.79  thf('65', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 29.50/29.79      inference('sup+', [status(thm)], ['63', '64'])).
% 29.50/29.79  thf('66', plain,
% 29.50/29.79      (![X50 : $i, X51 : $i]:
% 29.50/29.79         ((k1_setfam_1 @ (k2_tarski @ X50 @ X51)) = (k3_xboole_0 @ X50 @ X51))),
% 29.50/29.79      inference('cnf', [status(esa)], [t12_setfam_1])).
% 29.50/29.79  thf('67', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.50/29.79      inference('sup+', [status(thm)], ['65', '66'])).
% 29.50/29.79  thf(t51_xboole_1, axiom,
% 29.50/29.79    (![A:$i,B:$i]:
% 29.50/29.79     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 29.50/29.79       ( A ) ))).
% 29.50/29.79  thf('68', plain,
% 29.50/29.79      (![X18 : $i, X19 : $i]:
% 29.50/29.79         ((k2_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ (k4_xboole_0 @ X18 @ X19))
% 29.50/29.79           = (X18))),
% 29.50/29.79      inference('cnf', [status(esa)], [t51_xboole_1])).
% 29.50/29.79  thf('69', plain,
% 29.50/29.79      (![X42 : $i, X43 : $i]:
% 29.50/29.79         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 29.50/29.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 29.50/29.79  thf(commutativity_k2_xboole_0, axiom,
% 29.50/29.79    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 29.50/29.79  thf('70', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.50/29.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.50/29.79  thf('71', plain,
% 29.50/29.79      (![X18 : $i, X19 : $i]:
% 29.50/29.79         ((k2_xboole_0 @ (k6_subset_1 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X19))
% 29.50/29.79           = (X18))),
% 29.50/29.79      inference('demod', [status(thm)], ['68', '69', '70'])).
% 29.50/29.79  thf('72', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 29.50/29.79           = (X0))),
% 29.50/29.79      inference('sup+', [status(thm)], ['67', '71'])).
% 29.50/29.79  thf('73', plain,
% 29.50/29.79      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 29.50/29.79          (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))
% 29.50/29.79          = (k2_pre_topc @ sk_A @ sk_B_1)))
% 29.50/29.79         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.79                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.79                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 29.50/29.79      inference('sup+', [status(thm)], ['62', '72'])).
% 29.50/29.79  thf('74', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.50/29.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.50/29.79  thf(t7_xboole_1, axiom,
% 29.50/29.79    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 29.50/29.79  thf('75', plain,
% 29.50/29.79      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 29.50/29.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 29.50/29.79  thf('76', plain,
% 29.50/29.79      (![X52 : $i, X54 : $i]:
% 29.50/29.79         ((m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X52 @ X54))),
% 29.50/29.79      inference('cnf', [status(esa)], [t3_subset])).
% 29.50/29.79  thf('77', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['75', '76'])).
% 29.50/29.79  thf('78', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.50/29.79      inference('sup+', [status(thm)], ['74', '77'])).
% 29.50/29.79  thf('79', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['75', '76'])).
% 29.50/29.79  thf(t32_subset_1, axiom,
% 29.50/29.79    (![A:$i,B:$i]:
% 29.50/29.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 29.50/29.79       ( ![C:$i]:
% 29.50/29.79         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 29.50/29.79           ( ( k7_subset_1 @ A @ B @ C ) =
% 29.50/29.79             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 29.50/29.79  thf('80', plain,
% 29.50/29.79      (![X47 : $i, X48 : $i, X49 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 29.50/29.79          | ((k7_subset_1 @ X48 @ X49 @ X47)
% 29.50/29.79              = (k9_subset_1 @ X48 @ X49 @ (k3_subset_1 @ X48 @ X47)))
% 29.50/29.79          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 29.50/29.79      inference('cnf', [status(esa)], [t32_subset_1])).
% 29.50/29.79  thf('81', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 29.50/29.79          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X1)
% 29.50/29.79              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 29.50/29.79                 (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))))),
% 29.50/29.79      inference('sup-', [status(thm)], ['79', '80'])).
% 29.50/29.79  thf('82', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['75', '76'])).
% 29.50/29.79  thf(d5_subset_1, axiom,
% 29.50/29.79    (![A:$i,B:$i]:
% 29.50/29.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 29.50/29.79       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 29.50/29.79  thf('83', plain,
% 29.50/29.79      (![X24 : $i, X25 : $i]:
% 29.50/29.79         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 29.50/29.79          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 29.50/29.79      inference('cnf', [status(esa)], [d5_subset_1])).
% 29.50/29.79  thf('84', plain,
% 29.50/29.79      (![X42 : $i, X43 : $i]:
% 29.50/29.79         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 29.50/29.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 29.50/29.79  thf('85', plain,
% 29.50/29.79      (![X24 : $i, X25 : $i]:
% 29.50/29.79         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 29.50/29.79          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 29.50/29.79      inference('demod', [status(thm)], ['83', '84'])).
% 29.50/29.79  thf('86', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 29.50/29.79           = (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 29.50/29.79      inference('sup-', [status(thm)], ['82', '85'])).
% 29.50/29.79  thf('87', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 29.50/29.79          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X1)
% 29.50/29.79              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 29.50/29.79                 (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))))),
% 29.50/29.79      inference('demod', [status(thm)], ['81', '86'])).
% 29.50/29.79  thf('88', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X1)
% 29.50/29.79           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ 
% 29.50/29.79              (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['78', '87'])).
% 29.50/29.79  thf('89', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.50/29.79      inference('sup+', [status(thm)], ['74', '77'])).
% 29.50/29.79  thf('90', plain,
% 29.50/29.79      (![X44 : $i, X45 : $i, X46 : $i]:
% 29.50/29.79         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 29.50/29.79          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k6_subset_1 @ X44 @ X46)))),
% 29.50/29.79      inference('demod', [status(thm)], ['20', '21'])).
% 29.50/29.79  thf('91', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.50/29.79         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ X2)
% 29.50/29.79           = (k6_subset_1 @ X0 @ X2))),
% 29.50/29.79      inference('sup-', [status(thm)], ['89', '90'])).
% 29.50/29.79  thf('92', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k6_subset_1 @ X0 @ X1)
% 29.50/29.79           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ 
% 29.50/29.79              (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 29.50/29.79      inference('demod', [status(thm)], ['88', '91'])).
% 29.50/29.79  thf('93', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['75', '76'])).
% 29.50/29.79  thf(involutiveness_k3_subset_1, axiom,
% 29.50/29.79    (![A:$i,B:$i]:
% 29.50/29.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 29.50/29.79       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 29.50/29.79  thf('94', plain,
% 29.50/29.79      (![X37 : $i, X38 : $i]:
% 29.50/29.79         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 29.50/29.79          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 29.50/29.79      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 29.50/29.79  thf('95', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 29.50/29.79           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 29.50/29.79      inference('sup-', [status(thm)], ['93', '94'])).
% 29.50/29.79  thf('96', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 29.50/29.79           = (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 29.50/29.79      inference('sup-', [status(thm)], ['82', '85'])).
% 29.50/29.79  thf('97', plain,
% 29.50/29.79      (![X31 : $i, X32 : $i]:
% 29.50/29.79         (m1_subset_1 @ (k6_subset_1 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))),
% 29.50/29.79      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 29.50/29.79  thf('98', plain,
% 29.50/29.79      (![X24 : $i, X25 : $i]:
% 29.50/29.79         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 29.50/29.79          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 29.50/29.79      inference('demod', [status(thm)], ['83', '84'])).
% 29.50/29.79  thf('99', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 29.50/29.79           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['97', '98'])).
% 29.50/29.79  thf('100', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 29.50/29.79           (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 29.50/29.79      inference('demod', [status(thm)], ['95', '96', '99'])).
% 29.50/29.79  thf('101', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 29.50/29.79      inference('sup-', [status(thm)], ['25', '26'])).
% 29.50/29.79  thf(t43_xboole_1, axiom,
% 29.50/29.79    (![A:$i,B:$i,C:$i]:
% 29.50/29.79     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 29.50/29.79       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 29.50/29.79  thf('102', plain,
% 29.50/29.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 29.50/29.79         ((r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 29.50/29.79          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 29.50/29.79      inference('cnf', [status(esa)], [t43_xboole_1])).
% 29.50/29.79  thf('103', plain,
% 29.50/29.79      (![X42 : $i, X43 : $i]:
% 29.50/29.79         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 29.50/29.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 29.50/29.79  thf('104', plain,
% 29.50/29.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 29.50/29.79         ((r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X17)
% 29.50/29.79          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 29.50/29.79      inference('demod', [status(thm)], ['102', '103'])).
% 29.50/29.79  thf('105', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.50/29.79         (r1_tarski @ 
% 29.50/29.79          (k6_subset_1 @ (k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 29.50/29.79          X0)),
% 29.50/29.79      inference('sup-', [status(thm)], ['101', '104'])).
% 29.50/29.79  thf('106', plain,
% 29.50/29.79      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 29.50/29.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 29.50/29.79  thf('107', plain,
% 29.50/29.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 29.50/29.79         ((r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X17)
% 29.50/29.79          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 29.50/29.79      inference('demod', [status(thm)], ['102', '103'])).
% 29.50/29.79  thf('108', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 29.50/29.79      inference('sup-', [status(thm)], ['106', '107'])).
% 29.50/29.79  thf('109', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.50/29.79      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.50/29.79  thf(t1_boole, axiom,
% 29.50/29.79    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 29.50/29.79  thf('110', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 29.50/29.79      inference('cnf', [status(esa)], [t1_boole])).
% 29.50/29.79  thf('111', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.50/29.79      inference('sup+', [status(thm)], ['109', '110'])).
% 29.50/29.79  thf('112', plain,
% 29.50/29.79      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 29.50/29.79      inference('cnf', [status(esa)], [t7_xboole_1])).
% 29.50/29.79  thf('113', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 29.50/29.79      inference('sup+', [status(thm)], ['111', '112'])).
% 29.50/29.79  thf('114', plain,
% 29.50/29.79      (![X2 : $i, X4 : $i]:
% 29.50/29.79         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 29.50/29.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 29.50/29.79  thf('115', plain,
% 29.50/29.79      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['113', '114'])).
% 29.50/29.79  thf('116', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 29.50/29.79      inference('sup-', [status(thm)], ['108', '115'])).
% 29.50/29.79  thf('117', plain,
% 29.50/29.79      (![X18 : $i, X19 : $i]:
% 29.50/29.79         ((k2_xboole_0 @ (k6_subset_1 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X19))
% 29.50/29.79           = (X18))),
% 29.50/29.79      inference('demod', [status(thm)], ['68', '69', '70'])).
% 29.50/29.79  thf('118', plain,
% 29.50/29.79      (![X0 : $i]:
% 29.50/29.79         ((k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)) = (X0))),
% 29.50/29.79      inference('sup+', [status(thm)], ['116', '117'])).
% 29.50/29.79  thf('119', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.50/29.79      inference('sup+', [status(thm)], ['109', '110'])).
% 29.50/29.79  thf('120', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 29.50/29.79      inference('demod', [status(thm)], ['118', '119'])).
% 29.50/29.79  thf(t100_xboole_1, axiom,
% 29.50/29.79    (![A:$i,B:$i]:
% 29.50/29.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 29.50/29.79  thf('121', plain,
% 29.50/29.79      (![X5 : $i, X6 : $i]:
% 29.50/29.79         ((k4_xboole_0 @ X5 @ X6)
% 29.50/29.79           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 29.50/29.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 29.50/29.79  thf('122', plain,
% 29.50/29.79      (![X42 : $i, X43 : $i]:
% 29.50/29.79         ((k6_subset_1 @ X42 @ X43) = (k4_xboole_0 @ X42 @ X43))),
% 29.50/29.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 29.50/29.79  thf('123', plain,
% 29.50/29.79      (![X5 : $i, X6 : $i]:
% 29.50/29.79         ((k6_subset_1 @ X5 @ X6)
% 29.50/29.79           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 29.50/29.79      inference('demod', [status(thm)], ['121', '122'])).
% 29.50/29.79  thf('124', plain,
% 29.50/29.79      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 29.50/29.79      inference('sup+', [status(thm)], ['120', '123'])).
% 29.50/29.79  thf('125', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 29.50/29.79      inference('sup-', [status(thm)], ['108', '115'])).
% 29.50/29.79  thf('126', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 29.50/29.79      inference('sup+', [status(thm)], ['124', '125'])).
% 29.50/29.79  thf('127', plain,
% 29.50/29.79      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['113', '114'])).
% 29.50/29.79  thf('128', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 29.50/29.79      inference('sup-', [status(thm)], ['126', '127'])).
% 29.50/29.79  thf('129', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.50/29.79         ((k6_subset_1 @ 
% 29.50/29.79           (k6_subset_1 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X2) @ 
% 29.50/29.79           X1) = (k1_xboole_0))),
% 29.50/29.79      inference('sup-', [status(thm)], ['105', '128'])).
% 29.50/29.79  thf('130', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 29.50/29.79      inference('sup+', [status(thm)], ['124', '125'])).
% 29.50/29.79  thf('131', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 29.50/29.79      inference('cnf', [status(esa)], [t1_boole])).
% 29.50/29.79  thf('132', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 29.50/29.79      inference('sup+', [status(thm)], ['130', '131'])).
% 29.50/29.79  thf('133', plain,
% 29.50/29.79      (![X1 : $i, X2 : $i]:
% 29.50/29.79         ((k6_subset_1 @ (k6_subset_1 @ X1 @ X2) @ X1) = (k1_xboole_0))),
% 29.50/29.79      inference('demod', [status(thm)], ['129', '132'])).
% 29.50/29.79  thf('134', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 29.50/29.79      inference('sup+', [status(thm)], ['100', '133'])).
% 29.50/29.79  thf('135', plain,
% 29.50/29.79      (![X18 : $i, X19 : $i]:
% 29.50/29.79         ((k2_xboole_0 @ (k6_subset_1 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X19))
% 29.50/29.79           = (X18))),
% 29.50/29.79      inference('demod', [status(thm)], ['68', '69', '70'])).
% 29.50/29.79  thf('136', plain,
% 29.50/29.79      (![X0 : $i, X1 : $i]:
% 29.50/29.79         ((k2_xboole_0 @ k1_xboole_0 @ 
% 29.50/29.79           (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))) = (X0))),
% 29.50/29.79      inference('sup+', [status(thm)], ['134', '135'])).
% 29.50/29.79  thf('137', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['109', '110'])).
% 29.50/29.80  thf('138', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 29.50/29.80      inference('demod', [status(thm)], ['136', '137'])).
% 29.50/29.80  thf('139', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['65', '66'])).
% 29.50/29.80  thf('140', plain,
% 29.50/29.80      (![X5 : $i, X6 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X5 @ X6)
% 29.50/29.80           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 29.50/29.80      inference('demod', [status(thm)], ['121', '122'])).
% 29.50/29.80  thf('141', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ X1)
% 29.50/29.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 29.50/29.80      inference('sup+', [status(thm)], ['139', '140'])).
% 29.50/29.80  thf('142', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 29.50/29.80           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['138', '141'])).
% 29.50/29.80  thf('143', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ X1)
% 29.50/29.80           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0 @ 
% 29.50/29.80              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)))),
% 29.50/29.80      inference('demod', [status(thm)], ['92', '142'])).
% 29.50/29.80  thf('144', plain,
% 29.50/29.80      ((((k6_subset_1 @ 
% 29.50/29.80          (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 29.50/29.80          (k2_tops_1 @ sk_A @ sk_B_1))
% 29.50/29.80          = (k9_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 29.50/29.80             (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 29.50/29.80             (k5_xboole_0 @ 
% 29.50/29.80              (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 29.50/29.80               (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))) @ 
% 29.50/29.80              (k2_tops_1 @ sk_A @ sk_B_1)))))
% 29.50/29.80         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.80                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 29.50/29.80      inference('sup+', [status(thm)], ['73', '143'])).
% 29.50/29.80  thf('145', plain,
% 29.50/29.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.80  thf('146', plain,
% 29.50/29.80      (![X37 : $i, X38 : $i]:
% 29.50/29.80         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 29.50/29.80          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 29.50/29.80      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 29.50/29.80  thf('147', plain,
% 29.50/29.80      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 29.50/29.80      inference('sup-', [status(thm)], ['145', '146'])).
% 29.50/29.80  thf('148', plain,
% 29.50/29.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.80  thf('149', plain,
% 29.50/29.80      (![X24 : $i, X25 : $i]:
% 29.50/29.80         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 29.50/29.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 29.50/29.80      inference('demod', [status(thm)], ['83', '84'])).
% 29.50/29.80  thf('150', plain,
% 29.50/29.80      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 29.50/29.80         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 29.50/29.80      inference('sup-', [status(thm)], ['148', '149'])).
% 29.50/29.80  thf('151', plain,
% 29.50/29.80      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 29.50/29.80      inference('demod', [status(thm)], ['147', '150'])).
% 29.50/29.80  thf('152', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 29.50/29.80           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 29.50/29.80      inference('sup-', [status(thm)], ['97', '98'])).
% 29.50/29.80  thf('153', plain,
% 29.50/29.80      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 29.50/29.80      inference('demod', [status(thm)], ['151', '152'])).
% 29.50/29.80  thf('154', plain,
% 29.50/29.80      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 29.50/29.80      inference('cnf', [status(esa)], [t7_xboole_1])).
% 29.50/29.80  thf('155', plain,
% 29.50/29.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.80  thf('156', plain,
% 29.50/29.80      (![X52 : $i, X53 : $i]:
% 29.50/29.80         ((r1_tarski @ X52 @ X53) | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53)))),
% 29.50/29.80      inference('cnf', [status(esa)], [t3_subset])).
% 29.50/29.80  thf('157', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 29.50/29.80      inference('sup-', [status(thm)], ['155', '156'])).
% 29.50/29.80  thf(t1_xboole_1, axiom,
% 29.50/29.80    (![A:$i,B:$i,C:$i]:
% 29.50/29.80     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 29.50/29.80       ( r1_tarski @ A @ C ) ))).
% 29.50/29.80  thf('158', plain,
% 29.50/29.80      (![X8 : $i, X9 : $i, X10 : $i]:
% 29.50/29.80         (~ (r1_tarski @ X8 @ X9)
% 29.50/29.80          | ~ (r1_tarski @ X9 @ X10)
% 29.50/29.80          | (r1_tarski @ X8 @ X10))),
% 29.50/29.80      inference('cnf', [status(esa)], [t1_xboole_1])).
% 29.50/29.80  thf('159', plain,
% 29.50/29.80      (![X0 : $i]:
% 29.50/29.80         ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 29.50/29.80      inference('sup-', [status(thm)], ['157', '158'])).
% 29.50/29.80  thf('160', plain,
% 29.50/29.80      (![X0 : $i]:
% 29.50/29.80         (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 29.50/29.80      inference('sup-', [status(thm)], ['154', '159'])).
% 29.50/29.80  thf('161', plain,
% 29.50/29.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 29.50/29.80         ((r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X17)
% 29.50/29.80          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 29.50/29.80      inference('demod', [status(thm)], ['102', '103'])).
% 29.50/29.80  thf('162', plain,
% 29.50/29.80      (![X0 : $i]:
% 29.50/29.80         (r1_tarski @ (k6_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) @ X0)),
% 29.50/29.80      inference('sup-', [status(thm)], ['160', '161'])).
% 29.50/29.80  thf('163', plain,
% 29.50/29.80      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 29.50/29.80      inference('sup-', [status(thm)], ['113', '114'])).
% 29.50/29.80  thf('164', plain,
% 29.50/29.80      (((k6_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 29.50/29.80      inference('sup-', [status(thm)], ['162', '163'])).
% 29.50/29.80  thf('165', plain,
% 29.50/29.80      (![X18 : $i, X19 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ (k6_subset_1 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X19))
% 29.50/29.80           = (X18))),
% 29.50/29.80      inference('demod', [status(thm)], ['68', '69', '70'])).
% 29.50/29.80  thf('166', plain,
% 29.50/29.80      (((k2_xboole_0 @ k1_xboole_0 @ 
% 29.50/29.80         (k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A))) = (sk_B_1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['164', '165'])).
% 29.50/29.80  thf('167', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['109', '110'])).
% 29.50/29.80  thf('168', plain,
% 29.50/29.80      (((k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (sk_B_1))),
% 29.50/29.80      inference('demod', [status(thm)], ['166', '167'])).
% 29.50/29.80  thf('169', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ X1)
% 29.50/29.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 29.50/29.80      inference('sup+', [status(thm)], ['139', '140'])).
% 29.50/29.80  thf('170', plain,
% 29.50/29.80      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 29.50/29.80         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['168', '169'])).
% 29.50/29.80  thf('171', plain,
% 29.50/29.80      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 29.50/29.80      inference('demod', [status(thm)], ['153', '170'])).
% 29.50/29.80  thf('172', plain,
% 29.50/29.80      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 29.50/29.80        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.80      inference('demod', [status(thm)], ['46', '47'])).
% 29.50/29.80  thf('173', plain,
% 29.50/29.80      (![X31 : $i, X32 : $i]:
% 29.50/29.80         (m1_subset_1 @ (k6_subset_1 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))),
% 29.50/29.80      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 29.50/29.80  thf(redefinition_k4_subset_1, axiom,
% 29.50/29.80    (![A:$i,B:$i,C:$i]:
% 29.50/29.80     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 29.50/29.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 29.50/29.80       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 29.50/29.80  thf('174', plain,
% 29.50/29.80      (![X39 : $i, X40 : $i, X41 : $i]:
% 29.50/29.80         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 29.50/29.80          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 29.50/29.80          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 29.50/29.80      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 29.50/29.80  thf('175', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.50/29.80         (((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 29.50/29.80            = (k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X2))
% 29.50/29.80          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 29.50/29.80      inference('sup-', [status(thm)], ['173', '174'])).
% 29.50/29.80  thf('176', plain,
% 29.50/29.80      (![X0 : $i]:
% 29.50/29.80         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 29.50/29.80           (k2_tops_1 @ sk_A @ sk_B_1))
% 29.50/29.80           = (k2_xboole_0 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 29.50/29.80              (k2_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.80      inference('sup-', [status(thm)], ['172', '175'])).
% 29.50/29.80  thf('177', plain,
% 29.50/29.80      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 29.50/29.80         (k2_tops_1 @ sk_A @ sk_B_1))
% 29.50/29.80         = (k2_xboole_0 @ 
% 29.50/29.80            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 29.50/29.80            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.80      inference('sup+', [status(thm)], ['171', '176'])).
% 29.50/29.80  thf('178', plain,
% 29.50/29.80      (((k2_pre_topc @ sk_A @ sk_B_1)
% 29.50/29.80         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 29.50/29.80            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.80      inference('demod', [status(thm)], ['55', '56'])).
% 29.50/29.80  thf('179', plain,
% 29.50/29.80      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) = (sk_B_1))),
% 29.50/29.80      inference('demod', [status(thm)], ['153', '170'])).
% 29.50/29.80  thf('180', plain,
% 29.50/29.80      (((k2_pre_topc @ sk_A @ sk_B_1)
% 29.50/29.80         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.80      inference('demod', [status(thm)], ['177', '178', '179'])).
% 29.50/29.80  thf('181', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (X0))),
% 29.50/29.80      inference('demod', [status(thm)], ['136', '137'])).
% 29.50/29.80  thf('182', plain,
% 29.50/29.80      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['180', '181'])).
% 29.50/29.80  thf('183', plain,
% 29.50/29.80      (((k1_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.80         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.80      inference('demod', [status(thm)], ['17', '18', '23'])).
% 29.50/29.80  thf('184', plain,
% 29.50/29.80      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['180', '181'])).
% 29.50/29.80  thf('185', plain,
% 29.50/29.80      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['180', '181'])).
% 29.50/29.80  thf('186', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.50/29.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.50/29.80  thf('187', plain,
% 29.50/29.80      (((k2_pre_topc @ sk_A @ sk_B_1)
% 29.50/29.80         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 29.50/29.80      inference('demod', [status(thm)], ['177', '178', '179'])).
% 29.50/29.80  thf('188', plain,
% 29.50/29.80      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.80          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 29.50/29.80         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.80                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 29.50/29.80      inference('sup+', [status(thm)], ['60', '61'])).
% 29.50/29.80  thf('189', plain,
% 29.50/29.80      (![X1 : $i, X2 : $i]:
% 29.50/29.80         ((k6_subset_1 @ (k6_subset_1 @ X1 @ X2) @ X1) = (k1_xboole_0))),
% 29.50/29.80      inference('demod', [status(thm)], ['129', '132'])).
% 29.50/29.80  thf('190', plain,
% 29.50/29.80      (![X18 : $i, X19 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ (k6_subset_1 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X19))
% 29.50/29.80           = (X18))),
% 29.50/29.80      inference('demod', [status(thm)], ['68', '69', '70'])).
% 29.50/29.80  thf('191', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ k1_xboole_0 @ 
% 29.50/29.80           (k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X1))
% 29.50/29.80           = (k6_subset_1 @ X1 @ X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['189', '190'])).
% 29.50/29.80  thf('192', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['65', '66'])).
% 29.50/29.80  thf('193', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['109', '110'])).
% 29.50/29.80  thf('194', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 29.50/29.80           = (k6_subset_1 @ X1 @ X0))),
% 29.50/29.80      inference('demod', [status(thm)], ['191', '192', '193'])).
% 29.50/29.80  thf('195', plain,
% 29.50/29.80      (![X18 : $i, X19 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ (k6_subset_1 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X19))
% 29.50/29.80           = (X18))),
% 29.50/29.80      inference('demod', [status(thm)], ['68', '69', '70'])).
% 29.50/29.80  thf('196', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 29.50/29.80      inference('sup+', [status(thm)], ['74', '77'])).
% 29.50/29.80  thf('197', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['195', '196'])).
% 29.50/29.80  thf('198', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 29.50/29.80      inference('simplify', [status(thm)], ['12'])).
% 29.50/29.80  thf('199', plain,
% 29.50/29.80      (![X52 : $i, X54 : $i]:
% 29.50/29.80         ((m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X54)) | ~ (r1_tarski @ X52 @ X54))),
% 29.50/29.80      inference('cnf', [status(esa)], [t3_subset])).
% 29.50/29.80  thf('200', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 29.50/29.80      inference('sup-', [status(thm)], ['198', '199'])).
% 29.50/29.80  thf('201', plain,
% 29.50/29.80      (![X39 : $i, X40 : $i, X41 : $i]:
% 29.50/29.80         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 29.50/29.80          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X40))
% 29.50/29.80          | ((k4_subset_1 @ X40 @ X39 @ X41) = (k2_xboole_0 @ X39 @ X41)))),
% 29.50/29.80      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 29.50/29.80  thf('202', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 29.50/29.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 29.50/29.80      inference('sup-', [status(thm)], ['200', '201'])).
% 29.50/29.80  thf('203', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k4_subset_1 @ X0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 29.50/29.80           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 29.50/29.80      inference('sup-', [status(thm)], ['197', '202'])).
% 29.50/29.80  thf('204', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['195', '196'])).
% 29.50/29.80  thf('205', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 29.50/29.80      inference('sup-', [status(thm)], ['198', '199'])).
% 29.50/29.80  thf('206', plain,
% 29.50/29.80      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.50/29.80         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 29.50/29.80          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 29.50/29.80          | (m1_subset_1 @ (k4_subset_1 @ X29 @ X28 @ X30) @ 
% 29.50/29.80             (k1_zfmisc_1 @ X29)))),
% 29.50/29.80      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 29.50/29.80  thf('207', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 29.50/29.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 29.50/29.80      inference('sup-', [status(thm)], ['205', '206'])).
% 29.50/29.80  thf('208', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         (m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 29.50/29.80          (k1_zfmisc_1 @ X0))),
% 29.50/29.80      inference('sup-', [status(thm)], ['204', '207'])).
% 29.50/29.80  thf('209', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         (m1_subset_1 @ (k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 29.50/29.80          (k1_zfmisc_1 @ X1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['203', '208'])).
% 29.50/29.80  thf('210', plain,
% 29.50/29.80      (![X52 : $i, X53 : $i]:
% 29.50/29.80         ((r1_tarski @ X52 @ X53) | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53)))),
% 29.50/29.80      inference('cnf', [status(esa)], [t3_subset])).
% 29.50/29.80  thf('211', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         (r1_tarski @ (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) @ X0)),
% 29.50/29.80      inference('sup-', [status(thm)], ['209', '210'])).
% 29.50/29.80  thf('212', plain,
% 29.50/29.80      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 29.50/29.80      inference('cnf', [status(esa)], [t7_xboole_1])).
% 29.50/29.80  thf('213', plain,
% 29.50/29.80      (![X2 : $i, X4 : $i]:
% 29.50/29.80         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 29.50/29.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 29.50/29.80  thf('214', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 29.50/29.80          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 29.50/29.80      inference('sup-', [status(thm)], ['212', '213'])).
% 29.50/29.80  thf('215', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 29.50/29.80      inference('sup-', [status(thm)], ['211', '214'])).
% 29.50/29.80  thf('216', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)) = (X1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['194', '215'])).
% 29.50/29.80  thf('217', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 29.50/29.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 29.50/29.80  thf('218', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['100', '133'])).
% 29.50/29.80  thf('219', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['217', '218'])).
% 29.50/29.80  thf('220', plain,
% 29.50/29.80      (![X18 : $i, X19 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ (k6_subset_1 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X19))
% 29.50/29.80           = (X18))),
% 29.50/29.80      inference('demod', [status(thm)], ['68', '69', '70'])).
% 29.50/29.80  thf('221', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ k1_xboole_0 @ 
% 29.50/29.80           (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))) = (X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['219', '220'])).
% 29.50/29.80  thf('222', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['109', '110'])).
% 29.50/29.80  thf('223', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 29.50/29.80      inference('demod', [status(thm)], ['221', '222'])).
% 29.50/29.80  thf('224', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ X1)
% 29.50/29.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 29.50/29.80      inference('sup+', [status(thm)], ['139', '140'])).
% 29.50/29.80  thf('225', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 29.50/29.80           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['223', '224'])).
% 29.50/29.80  thf('226', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 29.50/29.80           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)) @ 
% 29.50/29.80              (k6_subset_1 @ X0 @ X1)))),
% 29.50/29.80      inference('sup+', [status(thm)], ['216', '225'])).
% 29.50/29.80  thf('227', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['65', '66'])).
% 29.50/29.80  thf('228', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['195', '196'])).
% 29.50/29.80  thf('229', plain,
% 29.50/29.80      (![X37 : $i, X38 : $i]:
% 29.50/29.80         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 29.50/29.80          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 29.50/29.80      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 29.50/29.80  thf('230', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 29.50/29.80           = (k3_xboole_0 @ X0 @ X1))),
% 29.50/29.80      inference('sup-', [status(thm)], ['228', '229'])).
% 29.50/29.80  thf('231', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['195', '196'])).
% 29.50/29.80  thf('232', plain,
% 29.50/29.80      (![X24 : $i, X25 : $i]:
% 29.50/29.80         (((k3_subset_1 @ X24 @ X25) = (k6_subset_1 @ X24 @ X25))
% 29.50/29.80          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 29.50/29.80      inference('demod', [status(thm)], ['83', '84'])).
% 29.50/29.80  thf('233', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 29.50/29.80           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 29.50/29.80      inference('sup-', [status(thm)], ['231', '232'])).
% 29.50/29.80  thf('234', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 29.50/29.80           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 29.50/29.80      inference('sup-', [status(thm)], ['97', '98'])).
% 29.50/29.80  thf('235', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 29.50/29.80           = (k3_xboole_0 @ X0 @ X1))),
% 29.50/29.80      inference('demod', [status(thm)], ['230', '233', '234'])).
% 29.50/29.80  thf('236', plain,
% 29.50/29.80      (![X1 : $i, X2 : $i]:
% 29.50/29.80         ((k6_subset_1 @ (k6_subset_1 @ X1 @ X2) @ X1) = (k1_xboole_0))),
% 29.50/29.80      inference('demod', [status(thm)], ['129', '132'])).
% 29.50/29.80  thf('237', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['235', '236'])).
% 29.50/29.80  thf('238', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['227', '237'])).
% 29.50/29.80  thf('239', plain,
% 29.50/29.80      (![X18 : $i, X19 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ (k6_subset_1 @ X18 @ X19) @ (k3_xboole_0 @ X18 @ X19))
% 29.50/29.80           = (X18))),
% 29.50/29.80      inference('demod', [status(thm)], ['68', '69', '70'])).
% 29.50/29.80  thf('240', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ k1_xboole_0 @ 
% 29.50/29.80           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 29.50/29.80           = (k3_xboole_0 @ X1 @ X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['238', '239'])).
% 29.50/29.80  thf('241', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['65', '66'])).
% 29.50/29.80  thf('242', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 29.50/29.80      inference('sup+', [status(thm)], ['109', '110'])).
% 29.50/29.80  thf('243', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 29.50/29.80           = (k3_xboole_0 @ X1 @ X0))),
% 29.50/29.80      inference('demod', [status(thm)], ['240', '241', '242'])).
% 29.50/29.80  thf('244', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 29.50/29.80           = (k3_xboole_0 @ X0 @ X1))),
% 29.50/29.80      inference('demod', [status(thm)], ['230', '233', '234'])).
% 29.50/29.80  thf('245', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 29.50/29.80           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 29.50/29.80      inference('sup+', [status(thm)], ['243', '244'])).
% 29.50/29.80  thf('246', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 29.50/29.80           = (k3_xboole_0 @ X1 @ X0))),
% 29.50/29.80      inference('demod', [status(thm)], ['240', '241', '242'])).
% 29.50/29.80  thf('247', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 29.50/29.80           = (k3_xboole_0 @ X1 @ X0))),
% 29.50/29.80      inference('demod', [status(thm)], ['245', '246'])).
% 29.50/29.80  thf('248', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 29.50/29.80           = (k3_xboole_0 @ X1 @ X0))),
% 29.50/29.80      inference('demod', [status(thm)], ['240', '241', '242'])).
% 29.50/29.80  thf('249', plain,
% 29.50/29.80      (![X5 : $i, X6 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X5 @ X6)
% 29.50/29.80           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 29.50/29.80      inference('demod', [status(thm)], ['121', '122'])).
% 29.50/29.80  thf('250', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 29.50/29.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 29.50/29.80      inference('sup+', [status(thm)], ['248', '249'])).
% 29.50/29.80  thf('251', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ X1)
% 29.50/29.80           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 29.50/29.80      inference('sup+', [status(thm)], ['139', '140'])).
% 29.50/29.80  thf('252', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 29.50/29.80           = (k6_subset_1 @ X0 @ X1))),
% 29.50/29.80      inference('demod', [status(thm)], ['250', '251'])).
% 29.50/29.80  thf('253', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 29.50/29.80           = (k3_xboole_0 @ X1 @ X0))),
% 29.50/29.80      inference('demod', [status(thm)], ['247', '252'])).
% 29.50/29.80  thf('254', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k2_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)) = (X1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['194', '215'])).
% 29.50/29.80  thf('255', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]:
% 29.50/29.80         ((k3_xboole_0 @ X1 @ X0)
% 29.50/29.80           = (k5_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 29.50/29.80      inference('demod', [status(thm)], ['226', '253', '254'])).
% 29.50/29.80  thf('256', plain,
% 29.50/29.80      ((((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))
% 29.50/29.80          = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 29.50/29.80             (k2_tops_1 @ sk_A @ sk_B_1))))
% 29.50/29.80         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.80                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 29.50/29.80      inference('sup+', [status(thm)], ['188', '255'])).
% 29.50/29.80  thf('257', plain,
% 29.50/29.80      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 29.50/29.80      inference('sup+', [status(thm)], ['180', '181'])).
% 29.50/29.80  thf('258', plain,
% 29.50/29.80      ((((sk_B_1)
% 29.50/29.80          = (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 29.50/29.80             (k2_tops_1 @ sk_A @ sk_B_1))))
% 29.50/29.80         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.80                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 29.50/29.80      inference('demod', [status(thm)], ['256', '257'])).
% 29.50/29.80  thf('259', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 29.50/29.80      inference('sup-', [status(thm)], ['198', '199'])).
% 29.50/29.80  thf(idempotence_k9_subset_1, axiom,
% 29.50/29.80    (![A:$i,B:$i,C:$i]:
% 29.50/29.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 29.50/29.80       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 29.50/29.80  thf('260', plain,
% 29.50/29.80      (![X34 : $i, X35 : $i, X36 : $i]:
% 29.50/29.80         (((k9_subset_1 @ X35 @ X34 @ X34) = (X34))
% 29.50/29.80          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 29.50/29.80      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 29.50/29.80  thf('261', plain,
% 29.50/29.80      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 29.50/29.80      inference('sup-', [status(thm)], ['259', '260'])).
% 29.50/29.80  thf('262', plain,
% 29.50/29.80      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 29.50/29.80         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.80                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 29.50/29.80      inference('demod', [status(thm)],
% 29.50/29.80                ['144', '182', '183', '184', '185', '186', '187', '258', '261'])).
% 29.50/29.80  thf('263', plain,
% 29.50/29.80      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 29.50/29.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.80  thf(fc9_tops_1, axiom,
% 29.50/29.80    (![A:$i,B:$i]:
% 29.50/29.80     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 29.50/29.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 29.50/29.80       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 29.50/29.80  thf('264', plain,
% 29.50/29.80      (![X57 : $i, X58 : $i]:
% 29.50/29.80         (~ (l1_pre_topc @ X57)
% 29.50/29.80          | ~ (v2_pre_topc @ X57)
% 29.50/29.80          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 29.50/29.80          | (v3_pre_topc @ (k1_tops_1 @ X57 @ X58) @ X57))),
% 29.50/29.80      inference('cnf', [status(esa)], [fc9_tops_1])).
% 29.50/29.80  thf('265', plain,
% 29.50/29.80      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 29.50/29.80        | ~ (v2_pre_topc @ sk_A)
% 29.50/29.80        | ~ (l1_pre_topc @ sk_A))),
% 29.50/29.80      inference('sup-', [status(thm)], ['263', '264'])).
% 29.50/29.80  thf('266', plain, ((v2_pre_topc @ sk_A)),
% 29.50/29.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.80  thf('267', plain, ((l1_pre_topc @ sk_A)),
% 29.50/29.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.50/29.80  thf('268', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 29.50/29.80      inference('demod', [status(thm)], ['265', '266', '267'])).
% 29.50/29.80  thf('269', plain,
% 29.50/29.80      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 29.50/29.80         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.80                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 29.50/29.80      inference('sup+', [status(thm)], ['262', '268'])).
% 29.50/29.80  thf('270', plain,
% 29.50/29.80      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 29.50/29.80      inference('split', [status(esa)], ['0'])).
% 29.50/29.80  thf('271', plain,
% 29.50/29.80      (~
% 29.50/29.80       (((k2_tops_1 @ sk_A @ sk_B_1)
% 29.50/29.80          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 29.50/29.80             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 29.50/29.80       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 29.50/29.80      inference('sup-', [status(thm)], ['269', '270'])).
% 29.50/29.80  thf('272', plain, ($false),
% 29.50/29.80      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '271'])).
% 29.50/29.80  
% 29.50/29.80  % SZS output end Refutation
% 29.50/29.80  
% 29.60/29.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
