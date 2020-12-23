%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0UUG6dRI9q

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:34 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 548 expanded)
%              Number of leaves         :   36 ( 171 expanded)
%              Depth                    :   14
%              Number of atoms          : 1593 (7284 expanded)
%              Number of equality atoms :   92 ( 361 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v3_pre_topc @ X41 @ X42 )
      | ~ ( r1_tarski @ X41 @ X43 )
      | ( r1_tarski @ X41 @ ( k1_tops_1 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
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
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( ( k1_tops_1 @ X47 @ X46 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X47 ) @ X46 @ ( k2_tops_1 @ X47 @ X46 ) ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k6_subset_1 @ X22 @ X24 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

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
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k2_tops_1 @ X40 @ X39 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k2_pre_topc @ X40 @ X39 ) @ ( k1_tops_1 @ X40 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
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

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('40',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X10 @ X9 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('49',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k2_pre_topc @ X45 @ X44 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 @ ( k2_tops_1 @ X45 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k6_subset_1 @ X22 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['38','55'])).

thf('57',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('68',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('69',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X27 @ X25 )
        = ( k9_subset_1 @ X26 @ X27 @ ( k3_subset_1 @ X26 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('74',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k6_subset_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k6_subset_1 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('79',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k6_subset_1 @ X22 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      = ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k6_subset_1 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('83',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('85',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X16 @ X15 @ X15 )
        = X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( ( k6_subset_1 @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['66','87'])).

thf('89',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('91',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ X33 @ ( k2_pre_topc @ X34 @ X33 ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('97',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('98',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k6_subset_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('101',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('103',plain,
    ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['98','101','102'])).

thf('104',plain,
    ( ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['89','103'])).

thf('105',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('106',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('107',plain,
    ( ( ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['89','103'])).

thf('108',plain,
    ( ( ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['88','104','105','106','107'])).

thf('109',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('110',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('112',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X37 @ X38 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('113',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['110','116'])).

thf('118',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('119',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','62','63','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0UUG6dRI9q
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.54/2.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.54/2.71  % Solved by: fo/fo7.sh
% 2.54/2.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.54/2.71  % done 2413 iterations in 2.251s
% 2.54/2.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.54/2.71  % SZS output start Refutation
% 2.54/2.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.54/2.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.54/2.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.54/2.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.54/2.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.54/2.71  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 2.54/2.71  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.54/2.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.54/2.71  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.54/2.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.54/2.71  thf(sk_A_type, type, sk_A: $i).
% 2.54/2.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.54/2.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.54/2.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.54/2.71  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 2.54/2.71  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.54/2.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.54/2.71  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.54/2.71  thf(t76_tops_1, conjecture,
% 2.54/2.71    (![A:$i]:
% 2.54/2.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.54/2.71       ( ![B:$i]:
% 2.54/2.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.54/2.71           ( ( v3_pre_topc @ B @ A ) <=>
% 2.54/2.71             ( ( k2_tops_1 @ A @ B ) =
% 2.54/2.71               ( k7_subset_1 @
% 2.54/2.71                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 2.54/2.71  thf(zf_stmt_0, negated_conjecture,
% 2.54/2.71    (~( ![A:$i]:
% 2.54/2.71        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.54/2.71          ( ![B:$i]:
% 2.54/2.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.54/2.71              ( ( v3_pre_topc @ B @ A ) <=>
% 2.54/2.71                ( ( k2_tops_1 @ A @ B ) =
% 2.54/2.71                  ( k7_subset_1 @
% 2.54/2.71                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 2.54/2.71    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 2.54/2.71  thf('0', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 2.54/2.71        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('1', plain,
% 2.54/2.71      (~
% 2.54/2.71       (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 2.54/2.71       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.54/2.71      inference('split', [status(esa)], ['0'])).
% 2.54/2.71  thf('2', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('3', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 2.54/2.71        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('4', plain,
% 2.54/2.71      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.54/2.71      inference('split', [status(esa)], ['3'])).
% 2.54/2.71  thf('5', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf(t56_tops_1, axiom,
% 2.54/2.71    (![A:$i]:
% 2.54/2.71     ( ( l1_pre_topc @ A ) =>
% 2.54/2.71       ( ![B:$i]:
% 2.54/2.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.54/2.71           ( ![C:$i]:
% 2.54/2.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.54/2.71               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 2.54/2.71                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.54/2.71  thf('6', plain,
% 2.54/2.71      (![X41 : $i, X42 : $i, X43 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 2.54/2.71          | ~ (v3_pre_topc @ X41 @ X42)
% 2.54/2.71          | ~ (r1_tarski @ X41 @ X43)
% 2.54/2.71          | (r1_tarski @ X41 @ (k1_tops_1 @ X42 @ X43))
% 2.54/2.71          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 2.54/2.71          | ~ (l1_pre_topc @ X42))),
% 2.54/2.71      inference('cnf', [status(esa)], [t56_tops_1])).
% 2.54/2.71  thf('7', plain,
% 2.54/2.71      (![X0 : $i]:
% 2.54/2.71         (~ (l1_pre_topc @ sk_A)
% 2.54/2.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.54/2.71          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 2.54/2.71          | ~ (r1_tarski @ sk_B_1 @ X0)
% 2.54/2.71          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.54/2.71      inference('sup-', [status(thm)], ['5', '6'])).
% 2.54/2.71  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('9', plain,
% 2.54/2.71      (![X0 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.54/2.71          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 2.54/2.71          | ~ (r1_tarski @ sk_B_1 @ X0)
% 2.54/2.71          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.54/2.71      inference('demod', [status(thm)], ['7', '8'])).
% 2.54/2.71  thf('10', plain,
% 2.54/2.71      ((![X0 : $i]:
% 2.54/2.71          (~ (r1_tarski @ sk_B_1 @ X0)
% 2.54/2.71           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 2.54/2.71           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 2.54/2.71         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['4', '9'])).
% 2.54/2.71  thf('11', plain,
% 2.54/2.71      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 2.54/2.71         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 2.54/2.71         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['2', '10'])).
% 2.54/2.71  thf(d10_xboole_0, axiom,
% 2.54/2.71    (![A:$i,B:$i]:
% 2.54/2.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.54/2.71  thf('12', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.54/2.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.54/2.71  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.54/2.71      inference('simplify', [status(thm)], ['12'])).
% 2.54/2.71  thf('14', plain,
% 2.54/2.71      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 2.54/2.71         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.54/2.71      inference('demod', [status(thm)], ['11', '13'])).
% 2.54/2.71  thf('15', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf(t74_tops_1, axiom,
% 2.54/2.71    (![A:$i]:
% 2.54/2.71     ( ( l1_pre_topc @ A ) =>
% 2.54/2.71       ( ![B:$i]:
% 2.54/2.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.54/2.71           ( ( k1_tops_1 @ A @ B ) =
% 2.54/2.71             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.54/2.71  thf('16', plain,
% 2.54/2.71      (![X46 : $i, X47 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 2.54/2.71          | ((k1_tops_1 @ X47 @ X46)
% 2.54/2.71              = (k7_subset_1 @ (u1_struct_0 @ X47) @ X46 @ 
% 2.54/2.71                 (k2_tops_1 @ X47 @ X46)))
% 2.54/2.71          | ~ (l1_pre_topc @ X47))),
% 2.54/2.71      inference('cnf', [status(esa)], [t74_tops_1])).
% 2.54/2.71  thf('17', plain,
% 2.54/2.71      ((~ (l1_pre_topc @ sk_A)
% 2.54/2.71        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 2.54/2.71               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 2.54/2.71      inference('sup-', [status(thm)], ['15', '16'])).
% 2.54/2.71  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('19', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf(redefinition_k7_subset_1, axiom,
% 2.54/2.71    (![A:$i,B:$i,C:$i]:
% 2.54/2.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.54/2.71       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.54/2.71  thf('20', plain,
% 2.54/2.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 2.54/2.71          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 2.54/2.71      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.54/2.71  thf(redefinition_k6_subset_1, axiom,
% 2.54/2.71    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.54/2.71  thf('21', plain,
% 2.54/2.71      (![X20 : $i, X21 : $i]:
% 2.54/2.71         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 2.54/2.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.54/2.71  thf('22', plain,
% 2.54/2.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 2.54/2.71          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k6_subset_1 @ X22 @ X24)))),
% 2.54/2.71      inference('demod', [status(thm)], ['20', '21'])).
% 2.54/2.71  thf('23', plain,
% 2.54/2.71      (![X0 : $i]:
% 2.54/2.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 2.54/2.71           = (k6_subset_1 @ sk_B_1 @ X0))),
% 2.54/2.71      inference('sup-', [status(thm)], ['19', '22'])).
% 2.54/2.71  thf('24', plain,
% 2.54/2.71      (((k1_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 2.54/2.71      inference('demod', [status(thm)], ['17', '18', '23'])).
% 2.54/2.71  thf(dt_k6_subset_1, axiom,
% 2.54/2.71    (![A:$i,B:$i]:
% 2.54/2.71     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.54/2.71  thf('25', plain,
% 2.54/2.71      (![X12 : $i, X13 : $i]:
% 2.54/2.71         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 2.54/2.71      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 2.54/2.71  thf(t3_subset, axiom,
% 2.54/2.71    (![A:$i,B:$i]:
% 2.54/2.71     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.54/2.71  thf('26', plain,
% 2.54/2.71      (![X30 : $i, X31 : $i]:
% 2.54/2.71         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 2.54/2.71      inference('cnf', [status(esa)], [t3_subset])).
% 2.54/2.71  thf('27', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 2.54/2.71      inference('sup-', [status(thm)], ['25', '26'])).
% 2.54/2.71  thf('28', plain,
% 2.54/2.71      (![X0 : $i, X2 : $i]:
% 2.54/2.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.54/2.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.54/2.71  thf('29', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i]:
% 2.54/2.71         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 2.54/2.71          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['27', '28'])).
% 2.54/2.71  thf('30', plain,
% 2.54/2.71      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 2.54/2.71        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 2.54/2.71      inference('sup-', [status(thm)], ['24', '29'])).
% 2.54/2.71  thf('31', plain,
% 2.54/2.71      (((k1_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 2.54/2.71      inference('demod', [status(thm)], ['17', '18', '23'])).
% 2.54/2.71  thf('32', plain,
% 2.54/2.71      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 2.54/2.71        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 2.54/2.71      inference('demod', [status(thm)], ['30', '31'])).
% 2.54/2.71  thf('33', plain,
% 2.54/2.71      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 2.54/2.71         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['14', '32'])).
% 2.54/2.71  thf('34', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf(l78_tops_1, axiom,
% 2.54/2.71    (![A:$i]:
% 2.54/2.71     ( ( l1_pre_topc @ A ) =>
% 2.54/2.71       ( ![B:$i]:
% 2.54/2.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.54/2.71           ( ( k2_tops_1 @ A @ B ) =
% 2.54/2.71             ( k7_subset_1 @
% 2.54/2.71               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 2.54/2.71               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.54/2.71  thf('35', plain,
% 2.54/2.71      (![X39 : $i, X40 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 2.54/2.71          | ((k2_tops_1 @ X40 @ X39)
% 2.54/2.71              = (k7_subset_1 @ (u1_struct_0 @ X40) @ 
% 2.54/2.71                 (k2_pre_topc @ X40 @ X39) @ (k1_tops_1 @ X40 @ X39)))
% 2.54/2.71          | ~ (l1_pre_topc @ X40))),
% 2.54/2.71      inference('cnf', [status(esa)], [l78_tops_1])).
% 2.54/2.71  thf('36', plain,
% 2.54/2.71      ((~ (l1_pre_topc @ sk_A)
% 2.54/2.71        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 2.54/2.71      inference('sup-', [status(thm)], ['34', '35'])).
% 2.54/2.71  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('38', plain,
% 2.54/2.71      (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 2.54/2.71      inference('demod', [status(thm)], ['36', '37'])).
% 2.54/2.71  thf('39', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf(dt_k2_tops_1, axiom,
% 2.54/2.71    (![A:$i,B:$i]:
% 2.54/2.71     ( ( ( l1_pre_topc @ A ) & 
% 2.54/2.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.54/2.71       ( m1_subset_1 @
% 2.54/2.71         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.54/2.71  thf('40', plain,
% 2.54/2.71      (![X35 : $i, X36 : $i]:
% 2.54/2.71         (~ (l1_pre_topc @ X35)
% 2.54/2.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 2.54/2.71          | (m1_subset_1 @ (k2_tops_1 @ X35 @ X36) @ 
% 2.54/2.71             (k1_zfmisc_1 @ (u1_struct_0 @ X35))))),
% 2.54/2.71      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 2.54/2.71  thf('41', plain,
% 2.54/2.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 2.54/2.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.54/2.71        | ~ (l1_pre_topc @ sk_A))),
% 2.54/2.71      inference('sup-', [status(thm)], ['39', '40'])).
% 2.54/2.71  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('43', plain,
% 2.54/2.71      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 2.54/2.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('demod', [status(thm)], ['41', '42'])).
% 2.54/2.71  thf('44', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf(dt_k4_subset_1, axiom,
% 2.54/2.71    (![A:$i,B:$i,C:$i]:
% 2.54/2.71     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.54/2.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.54/2.71       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.54/2.71  thf('45', plain,
% 2.54/2.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 2.54/2.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10))
% 2.54/2.71          | (m1_subset_1 @ (k4_subset_1 @ X10 @ X9 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 2.54/2.71      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 2.54/2.71  thf('46', plain,
% 2.54/2.71      (![X0 : $i]:
% 2.54/2.71         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 2.54/2.71           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.54/2.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.54/2.71      inference('sup-', [status(thm)], ['44', '45'])).
% 2.54/2.71  thf('47', plain,
% 2.54/2.71      ((m1_subset_1 @ 
% 2.54/2.71        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 2.54/2.71         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 2.54/2.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['43', '46'])).
% 2.54/2.71  thf('48', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf(t65_tops_1, axiom,
% 2.54/2.71    (![A:$i]:
% 2.54/2.71     ( ( l1_pre_topc @ A ) =>
% 2.54/2.71       ( ![B:$i]:
% 2.54/2.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.54/2.71           ( ( k2_pre_topc @ A @ B ) =
% 2.54/2.71             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 2.54/2.71  thf('49', plain,
% 2.54/2.71      (![X44 : $i, X45 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 2.54/2.71          | ((k2_pre_topc @ X45 @ X44)
% 2.54/2.71              = (k4_subset_1 @ (u1_struct_0 @ X45) @ X44 @ 
% 2.54/2.71                 (k2_tops_1 @ X45 @ X44)))
% 2.54/2.71          | ~ (l1_pre_topc @ X45))),
% 2.54/2.71      inference('cnf', [status(esa)], [t65_tops_1])).
% 2.54/2.71  thf('50', plain,
% 2.54/2.71      ((~ (l1_pre_topc @ sk_A)
% 2.54/2.71        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 2.54/2.71            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 2.54/2.71               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 2.54/2.71      inference('sup-', [status(thm)], ['48', '49'])).
% 2.54/2.71  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('52', plain,
% 2.54/2.71      (((k2_pre_topc @ sk_A @ sk_B_1)
% 2.54/2.71         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 2.54/2.71            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 2.54/2.71      inference('demod', [status(thm)], ['50', '51'])).
% 2.54/2.71  thf('53', plain,
% 2.54/2.71      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.54/2.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('demod', [status(thm)], ['47', '52'])).
% 2.54/2.71  thf('54', plain,
% 2.54/2.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 2.54/2.71          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k6_subset_1 @ X22 @ X24)))),
% 2.54/2.71      inference('demod', [status(thm)], ['20', '21'])).
% 2.54/2.71  thf('55', plain,
% 2.54/2.71      (![X0 : $i]:
% 2.54/2.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 2.54/2.71           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 2.54/2.71      inference('sup-', [status(thm)], ['53', '54'])).
% 2.54/2.71  thf('56', plain,
% 2.54/2.71      (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.54/2.71            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 2.54/2.71      inference('demod', [status(thm)], ['38', '55'])).
% 2.54/2.71  thf('57', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.54/2.71         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.54/2.71      inference('sup+', [status(thm)], ['33', '56'])).
% 2.54/2.71  thf('58', plain,
% 2.54/2.71      (![X0 : $i]:
% 2.54/2.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 2.54/2.71           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 2.54/2.71      inference('sup-', [status(thm)], ['53', '54'])).
% 2.54/2.71  thf('59', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.54/2.71         <= (~
% 2.54/2.71             (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('split', [status(esa)], ['0'])).
% 2.54/2.71  thf('60', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          != (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.54/2.71         <= (~
% 2.54/2.71             (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('sup-', [status(thm)], ['58', '59'])).
% 2.54/2.71  thf('61', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 2.54/2.71         <= (~
% 2.54/2.71             (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 2.54/2.71             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['57', '60'])).
% 2.54/2.71  thf('62', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 2.54/2.71       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.54/2.71      inference('simplify', [status(thm)], ['61'])).
% 2.54/2.71  thf('63', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 2.54/2.71       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.54/2.71      inference('split', [status(esa)], ['3'])).
% 2.54/2.71  thf('64', plain,
% 2.54/2.71      (![X0 : $i]:
% 2.54/2.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 2.54/2.71           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 2.54/2.71      inference('sup-', [status(thm)], ['53', '54'])).
% 2.54/2.71  thf('65', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('split', [status(esa)], ['3'])).
% 2.54/2.71  thf('66', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('sup+', [status(thm)], ['64', '65'])).
% 2.54/2.71  thf('67', plain,
% 2.54/2.71      (![X12 : $i, X13 : $i]:
% 2.54/2.71         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 2.54/2.71      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 2.54/2.71  thf('68', plain,
% 2.54/2.71      (![X12 : $i, X13 : $i]:
% 2.54/2.71         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 2.54/2.71      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 2.54/2.71  thf(t32_subset_1, axiom,
% 2.54/2.71    (![A:$i,B:$i]:
% 2.54/2.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.54/2.71       ( ![C:$i]:
% 2.54/2.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.54/2.71           ( ( k7_subset_1 @ A @ B @ C ) =
% 2.54/2.71             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 2.54/2.71  thf('69', plain,
% 2.54/2.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 2.54/2.71          | ((k7_subset_1 @ X26 @ X27 @ X25)
% 2.54/2.71              = (k9_subset_1 @ X26 @ X27 @ (k3_subset_1 @ X26 @ X25)))
% 2.54/2.71          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 2.54/2.71      inference('cnf', [status(esa)], [t32_subset_1])).
% 2.54/2.71  thf('70', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 2.54/2.71          | ((k7_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 2.54/2.71              = (k9_subset_1 @ X0 @ X2 @ 
% 2.54/2.71                 (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))))),
% 2.54/2.71      inference('sup-', [status(thm)], ['68', '69'])).
% 2.54/2.71  thf('71', plain,
% 2.54/2.71      (![X12 : $i, X13 : $i]:
% 2.54/2.71         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 2.54/2.71      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 2.54/2.71  thf(d5_subset_1, axiom,
% 2.54/2.71    (![A:$i,B:$i]:
% 2.54/2.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.54/2.71       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.54/2.71  thf('72', plain,
% 2.54/2.71      (![X5 : $i, X6 : $i]:
% 2.54/2.71         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 2.54/2.71          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 2.54/2.71      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.54/2.71  thf('73', plain,
% 2.54/2.71      (![X20 : $i, X21 : $i]:
% 2.54/2.71         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 2.54/2.71      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 2.54/2.71  thf('74', plain,
% 2.54/2.71      (![X5 : $i, X6 : $i]:
% 2.54/2.71         (((k3_subset_1 @ X5 @ X6) = (k6_subset_1 @ X5 @ X6))
% 2.54/2.71          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 2.54/2.71      inference('demod', [status(thm)], ['72', '73'])).
% 2.54/2.71  thf('75', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i]:
% 2.54/2.71         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 2.54/2.71           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['71', '74'])).
% 2.54/2.71  thf('76', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 2.54/2.71          | ((k7_subset_1 @ X0 @ X2 @ (k6_subset_1 @ X0 @ X1))
% 2.54/2.71              = (k9_subset_1 @ X0 @ X2 @ 
% 2.54/2.71                 (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))))),
% 2.54/2.71      inference('demod', [status(thm)], ['70', '75'])).
% 2.54/2.71  thf('77', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.71         ((k7_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ (k6_subset_1 @ X0 @ X2))
% 2.54/2.71           = (k9_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ 
% 2.54/2.71              (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X2))))),
% 2.54/2.71      inference('sup-', [status(thm)], ['67', '76'])).
% 2.54/2.71  thf('78', plain,
% 2.54/2.71      (![X12 : $i, X13 : $i]:
% 2.54/2.71         (m1_subset_1 @ (k6_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))),
% 2.54/2.71      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 2.54/2.71  thf('79', plain,
% 2.54/2.71      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 2.54/2.71          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k6_subset_1 @ X22 @ X24)))),
% 2.54/2.71      inference('demod', [status(thm)], ['20', '21'])).
% 2.54/2.71  thf('80', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.71         ((k7_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 2.54/2.71           = (k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X2))),
% 2.54/2.71      inference('sup-', [status(thm)], ['78', '79'])).
% 2.54/2.71  thf('81', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.71         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ (k6_subset_1 @ X0 @ X2))
% 2.54/2.71           = (k9_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ 
% 2.54/2.71              (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X2))))),
% 2.54/2.71      inference('demod', [status(thm)], ['77', '80'])).
% 2.54/2.71  thf('82', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.54/2.71      inference('simplify', [status(thm)], ['12'])).
% 2.54/2.71  thf('83', plain,
% 2.54/2.71      (![X30 : $i, X32 : $i]:
% 2.54/2.71         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 2.54/2.71      inference('cnf', [status(esa)], [t3_subset])).
% 2.54/2.71  thf('84', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.54/2.71      inference('sup-', [status(thm)], ['82', '83'])).
% 2.54/2.71  thf(idempotence_k9_subset_1, axiom,
% 2.54/2.71    (![A:$i,B:$i,C:$i]:
% 2.54/2.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.54/2.71       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 2.54/2.71  thf('85', plain,
% 2.54/2.71      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.54/2.71         (((k9_subset_1 @ X16 @ X15 @ X15) = (X15))
% 2.54/2.71          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 2.54/2.71      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 2.54/2.71  thf('86', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 2.54/2.71      inference('sup-', [status(thm)], ['84', '85'])).
% 2.54/2.71  thf('87', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i]:
% 2.54/2.71         ((k6_subset_1 @ (k6_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0)) @ 
% 2.54/2.71           (k6_subset_1 @ X1 @ X0))
% 2.54/2.71           = (k6_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 2.54/2.71      inference('sup+', [status(thm)], ['81', '86'])).
% 2.54/2.71  thf('88', plain,
% 2.54/2.71      ((((k6_subset_1 @ 
% 2.54/2.71          (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.54/2.71           (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 2.54/2.71          (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 2.54/2.71          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.54/2.71             (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('sup+', [status(thm)], ['66', '87'])).
% 2.54/2.71  thf('89', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('sup+', [status(thm)], ['64', '65'])).
% 2.54/2.71  thf('90', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf(t48_pre_topc, axiom,
% 2.54/2.71    (![A:$i]:
% 2.54/2.71     ( ( l1_pre_topc @ A ) =>
% 2.54/2.71       ( ![B:$i]:
% 2.54/2.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.54/2.71           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 2.54/2.71  thf('91', plain,
% 2.54/2.71      (![X33 : $i, X34 : $i]:
% 2.54/2.71         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 2.54/2.71          | (r1_tarski @ X33 @ (k2_pre_topc @ X34 @ X33))
% 2.54/2.71          | ~ (l1_pre_topc @ X34))),
% 2.54/2.71      inference('cnf', [status(esa)], [t48_pre_topc])).
% 2.54/2.71  thf('92', plain,
% 2.54/2.71      ((~ (l1_pre_topc @ sk_A)
% 2.54/2.71        | (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['90', '91'])).
% 2.54/2.71  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('94', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 2.54/2.71      inference('demod', [status(thm)], ['92', '93'])).
% 2.54/2.71  thf('95', plain,
% 2.54/2.71      (![X30 : $i, X32 : $i]:
% 2.54/2.71         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 2.54/2.71      inference('cnf', [status(esa)], [t3_subset])).
% 2.54/2.71  thf('96', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['94', '95'])).
% 2.54/2.71  thf(involutiveness_k3_subset_1, axiom,
% 2.54/2.71    (![A:$i,B:$i]:
% 2.54/2.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.54/2.71       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.54/2.71  thf('97', plain,
% 2.54/2.71      (![X18 : $i, X19 : $i]:
% 2.54/2.71         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 2.54/2.71          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 2.54/2.71      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.54/2.71  thf('98', plain,
% 2.54/2.71      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.54/2.71         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 2.54/2.71      inference('sup-', [status(thm)], ['96', '97'])).
% 2.54/2.71  thf('99', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['94', '95'])).
% 2.54/2.71  thf('100', plain,
% 2.54/2.71      (![X5 : $i, X6 : $i]:
% 2.54/2.71         (((k3_subset_1 @ X5 @ X6) = (k6_subset_1 @ X5 @ X6))
% 2.54/2.71          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 2.54/2.71      inference('demod', [status(thm)], ['72', '73'])).
% 2.54/2.71  thf('101', plain,
% 2.54/2.71      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 2.54/2.71         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 2.54/2.71      inference('sup-', [status(thm)], ['99', '100'])).
% 2.54/2.71  thf('102', plain,
% 2.54/2.71      (![X0 : $i, X1 : $i]:
% 2.54/2.71         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 2.54/2.71           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 2.54/2.71      inference('sup-', [status(thm)], ['71', '74'])).
% 2.54/2.71  thf('103', plain,
% 2.54/2.71      (((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.54/2.71         (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 2.54/2.71      inference('demod', [status(thm)], ['98', '101', '102'])).
% 2.54/2.71  thf('104', plain,
% 2.54/2.71      ((((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.54/2.71          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('sup+', [status(thm)], ['89', '103'])).
% 2.54/2.71  thf('105', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('sup+', [status(thm)], ['64', '65'])).
% 2.54/2.71  thf('106', plain,
% 2.54/2.71      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('sup+', [status(thm)], ['64', '65'])).
% 2.54/2.71  thf('107', plain,
% 2.54/2.71      ((((k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 2.54/2.71          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('sup+', [status(thm)], ['89', '103'])).
% 2.54/2.71  thf('108', plain,
% 2.54/2.71      ((((k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('demod', [status(thm)], ['88', '104', '105', '106', '107'])).
% 2.54/2.71  thf('109', plain,
% 2.54/2.71      (((k1_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 2.54/2.71      inference('demod', [status(thm)], ['17', '18', '23'])).
% 2.54/2.71  thf('110', plain,
% 2.54/2.71      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('sup+', [status(thm)], ['108', '109'])).
% 2.54/2.71  thf('111', plain,
% 2.54/2.71      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf(fc9_tops_1, axiom,
% 2.54/2.71    (![A:$i,B:$i]:
% 2.54/2.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.54/2.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.54/2.71       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 2.54/2.71  thf('112', plain,
% 2.54/2.71      (![X37 : $i, X38 : $i]:
% 2.54/2.71         (~ (l1_pre_topc @ X37)
% 2.54/2.71          | ~ (v2_pre_topc @ X37)
% 2.54/2.71          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.54/2.71          | (v3_pre_topc @ (k1_tops_1 @ X37 @ X38) @ X37))),
% 2.54/2.71      inference('cnf', [status(esa)], [fc9_tops_1])).
% 2.54/2.71  thf('113', plain,
% 2.54/2.71      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 2.54/2.71        | ~ (v2_pre_topc @ sk_A)
% 2.54/2.71        | ~ (l1_pre_topc @ sk_A))),
% 2.54/2.71      inference('sup-', [status(thm)], ['111', '112'])).
% 2.54/2.71  thf('114', plain, ((v2_pre_topc @ sk_A)),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 2.54/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.71  thf('116', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 2.54/2.71      inference('demod', [status(thm)], ['113', '114', '115'])).
% 2.54/2.71  thf('117', plain,
% 2.54/2.71      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 2.54/2.71         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 2.54/2.71      inference('sup+', [status(thm)], ['110', '116'])).
% 2.54/2.71  thf('118', plain,
% 2.54/2.71      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 2.54/2.71      inference('split', [status(esa)], ['0'])).
% 2.54/2.71  thf('119', plain,
% 2.54/2.71      (~
% 2.54/2.71       (((k2_tops_1 @ sk_A @ sk_B_1)
% 2.54/2.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.54/2.71             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 2.54/2.71       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 2.54/2.71      inference('sup-', [status(thm)], ['117', '118'])).
% 2.54/2.71  thf('120', plain, ($false),
% 2.54/2.71      inference('sat_resolution*', [status(thm)], ['1', '62', '63', '119'])).
% 2.54/2.71  
% 2.54/2.71  % SZS output end Refutation
% 2.54/2.71  
% 2.54/2.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
