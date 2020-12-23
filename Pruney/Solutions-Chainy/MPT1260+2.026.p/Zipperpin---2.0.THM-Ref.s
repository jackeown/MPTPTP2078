%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m6bj52jubm

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:26 EST 2020

% Result     : Theorem 3.75s
% Output     : Refutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 453 expanded)
%              Number of leaves         :   41 ( 152 expanded)
%              Depth                    :   17
%              Number of atoms          : 1564 (5294 expanded)
%              Number of equality atoms :   99 ( 320 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k1_tops_1 @ X56 @ X55 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k7_subset_1 @ X34 @ X33 @ X35 )
        = ( k4_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k6_subset_1 @ X31 @ X32 )
      = ( k4_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k7_subset_1 @ X34 @ X33 @ X35 )
        = ( k6_subset_1 @ X33 @ X35 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
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
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_tops_1 @ X49 @ X48 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X49 ) @ ( k2_pre_topc @ X49 @ X48 ) @ ( k1_tops_1 @ X49 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
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
    ! [X44: $i,X45: $i] :
      ( ~ ( l1_pre_topc @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X44 @ X45 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X20 @ X19 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
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
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k2_pre_topc @ X54 @ X53 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X54 ) @ X53 @ ( k2_tops_1 @ X54 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k7_subset_1 @ X34 @ X33 @ X35 )
        = ( k6_subset_1 @ X33 @ X35 ) ) ) ),
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

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X14 @ X13 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('67',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','70'])).

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
    ! [X31: $i,X32: $i] :
      ( ( k6_subset_1 @ X31 @ X32 )
      = ( k4_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k6_subset_1 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('76',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('77',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k6_subset_1 @ X31 @ X32 )
      = ( k4_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('78',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k6_subset_1 @ X31 @ X32 )
      = ( k4_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('79',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ ( k6_subset_1 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','79'])).

thf('81',plain,
    ( ( ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['62','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('83',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('84',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('85',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('87',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('89',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ ( k6_subset_1 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('91',plain,(
    ! [X22: $i,X23: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('94',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k4_subset_1 @ X29 @ X28 @ X30 )
        = ( k2_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['89','96'])).

thf('98',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('99',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('100',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('101',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('102',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['81','82','104'])).

thf('106',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('108',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','79'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf('115',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['105','114'])).

thf('116',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('117',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('119',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('121',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X46 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('122',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['119','125'])).

thf('127',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('128',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m6bj52jubm
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:41:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.75/3.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.75/3.98  % Solved by: fo/fo7.sh
% 3.75/3.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.75/3.98  % done 5453 iterations in 3.541s
% 3.75/3.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.75/3.98  % SZS output start Refutation
% 3.75/3.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.75/3.98  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.75/3.98  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.75/3.98  thf(sk_A_type, type, sk_A: $i).
% 3.75/3.98  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 3.75/3.98  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.75/3.98  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.75/3.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.75/3.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.75/3.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.75/3.98  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.75/3.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.75/3.98  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 3.75/3.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.75/3.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.75/3.98  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.75/3.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.75/3.98  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.75/3.98  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.75/3.98  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.75/3.98  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.75/3.98  thf(t76_tops_1, conjecture,
% 3.75/3.98    (![A:$i]:
% 3.75/3.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.75/3.98       ( ![B:$i]:
% 3.75/3.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.75/3.98           ( ( v3_pre_topc @ B @ A ) <=>
% 3.75/3.98             ( ( k2_tops_1 @ A @ B ) =
% 3.75/3.98               ( k7_subset_1 @
% 3.75/3.98                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 3.75/3.98  thf(zf_stmt_0, negated_conjecture,
% 3.75/3.98    (~( ![A:$i]:
% 3.75/3.98        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.75/3.98          ( ![B:$i]:
% 3.75/3.98            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.75/3.98              ( ( v3_pre_topc @ B @ A ) <=>
% 3.75/3.98                ( ( k2_tops_1 @ A @ B ) =
% 3.75/3.98                  ( k7_subset_1 @
% 3.75/3.98                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 3.75/3.98    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 3.75/3.98  thf('0', plain,
% 3.75/3.98      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 3.75/3.98        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf('1', plain,
% 3.75/3.98      (~
% 3.75/3.98       (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 3.75/3.98       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.75/3.98      inference('split', [status(esa)], ['0'])).
% 3.75/3.98  thf('2', plain,
% 3.75/3.98      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf('3', plain,
% 3.75/3.98      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 3.75/3.98        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf('4', plain,
% 3.75/3.98      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.75/3.98      inference('split', [status(esa)], ['3'])).
% 3.75/3.98  thf('5', plain,
% 3.75/3.98      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf(t56_tops_1, axiom,
% 3.75/3.98    (![A:$i]:
% 3.75/3.98     ( ( l1_pre_topc @ A ) =>
% 3.75/3.98       ( ![B:$i]:
% 3.75/3.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.75/3.98           ( ![C:$i]:
% 3.75/3.98             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.75/3.98               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 3.75/3.98                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.75/3.98  thf('6', plain,
% 3.75/3.98      (![X50 : $i, X51 : $i, X52 : $i]:
% 3.75/3.98         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 3.75/3.98          | ~ (v3_pre_topc @ X50 @ X51)
% 3.75/3.98          | ~ (r1_tarski @ X50 @ X52)
% 3.75/3.98          | (r1_tarski @ X50 @ (k1_tops_1 @ X51 @ X52))
% 3.75/3.98          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 3.75/3.98          | ~ (l1_pre_topc @ X51))),
% 3.75/3.98      inference('cnf', [status(esa)], [t56_tops_1])).
% 3.75/3.98  thf('7', plain,
% 3.75/3.98      (![X0 : $i]:
% 3.75/3.98         (~ (l1_pre_topc @ sk_A)
% 3.75/3.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.75/3.98          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 3.75/3.98          | ~ (r1_tarski @ sk_B_1 @ X0)
% 3.75/3.98          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.75/3.98      inference('sup-', [status(thm)], ['5', '6'])).
% 3.75/3.98  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf('9', plain,
% 3.75/3.98      (![X0 : $i]:
% 3.75/3.98         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.75/3.98          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 3.75/3.98          | ~ (r1_tarski @ sk_B_1 @ X0)
% 3.75/3.98          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.75/3.98      inference('demod', [status(thm)], ['7', '8'])).
% 3.75/3.98  thf('10', plain,
% 3.75/3.98      ((![X0 : $i]:
% 3.75/3.98          (~ (r1_tarski @ sk_B_1 @ X0)
% 3.75/3.98           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 3.75/3.98           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 3.75/3.98         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.75/3.98      inference('sup-', [status(thm)], ['4', '9'])).
% 3.75/3.98  thf('11', plain,
% 3.75/3.98      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 3.75/3.98         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 3.75/3.98         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.75/3.98      inference('sup-', [status(thm)], ['2', '10'])).
% 3.75/3.98  thf(d10_xboole_0, axiom,
% 3.75/3.98    (![A:$i,B:$i]:
% 3.75/3.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.75/3.98  thf('12', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.75/3.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.75/3.98  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.75/3.98      inference('simplify', [status(thm)], ['12'])).
% 3.75/3.98  thf('14', plain,
% 3.75/3.98      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 3.75/3.98         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.75/3.98      inference('demod', [status(thm)], ['11', '13'])).
% 3.75/3.98  thf('15', plain,
% 3.75/3.98      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf(t74_tops_1, axiom,
% 3.75/3.98    (![A:$i]:
% 3.75/3.98     ( ( l1_pre_topc @ A ) =>
% 3.75/3.98       ( ![B:$i]:
% 3.75/3.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.75/3.98           ( ( k1_tops_1 @ A @ B ) =
% 3.75/3.98             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.75/3.98  thf('16', plain,
% 3.75/3.98      (![X55 : $i, X56 : $i]:
% 3.75/3.98         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 3.75/3.98          | ((k1_tops_1 @ X56 @ X55)
% 3.75/3.98              = (k7_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 3.75/3.98                 (k2_tops_1 @ X56 @ X55)))
% 3.75/3.98          | ~ (l1_pre_topc @ X56))),
% 3.75/3.98      inference('cnf', [status(esa)], [t74_tops_1])).
% 3.75/3.98  thf('17', plain,
% 3.75/3.98      ((~ (l1_pre_topc @ sk_A)
% 3.75/3.98        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.75/3.98               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 3.75/3.98      inference('sup-', [status(thm)], ['15', '16'])).
% 3.75/3.98  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf('19', plain,
% 3.75/3.98      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf(redefinition_k7_subset_1, axiom,
% 3.75/3.98    (![A:$i,B:$i,C:$i]:
% 3.75/3.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.75/3.98       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.75/3.98  thf('20', plain,
% 3.75/3.98      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.75/3.98         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 3.75/3.98          | ((k7_subset_1 @ X34 @ X33 @ X35) = (k4_xboole_0 @ X33 @ X35)))),
% 3.75/3.98      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.75/3.98  thf(redefinition_k6_subset_1, axiom,
% 3.75/3.98    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 3.75/3.98  thf('21', plain,
% 3.75/3.98      (![X31 : $i, X32 : $i]:
% 3.75/3.98         ((k6_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))),
% 3.75/3.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.75/3.98  thf('22', plain,
% 3.75/3.98      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.75/3.98         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 3.75/3.98          | ((k7_subset_1 @ X34 @ X33 @ X35) = (k6_subset_1 @ X33 @ X35)))),
% 3.75/3.98      inference('demod', [status(thm)], ['20', '21'])).
% 3.75/3.98  thf('23', plain,
% 3.75/3.98      (![X0 : $i]:
% 3.75/3.98         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 3.75/3.98           = (k6_subset_1 @ sk_B_1 @ X0))),
% 3.75/3.98      inference('sup-', [status(thm)], ['19', '22'])).
% 3.75/3.98  thf('24', plain,
% 3.75/3.98      (((k1_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('demod', [status(thm)], ['17', '18', '23'])).
% 3.75/3.98  thf(dt_k6_subset_1, axiom,
% 3.75/3.98    (![A:$i,B:$i]:
% 3.75/3.98     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 3.75/3.98  thf('25', plain,
% 3.75/3.98      (![X22 : $i, X23 : $i]:
% 3.75/3.98         (m1_subset_1 @ (k6_subset_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))),
% 3.75/3.98      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 3.75/3.98  thf(t3_subset, axiom,
% 3.75/3.98    (![A:$i,B:$i]:
% 3.75/3.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.75/3.98  thf('26', plain,
% 3.75/3.98      (![X41 : $i, X42 : $i]:
% 3.75/3.98         ((r1_tarski @ X41 @ X42) | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 3.75/3.98      inference('cnf', [status(esa)], [t3_subset])).
% 3.75/3.98  thf('27', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 3.75/3.98      inference('sup-', [status(thm)], ['25', '26'])).
% 3.75/3.98  thf('28', plain,
% 3.75/3.98      (![X0 : $i, X2 : $i]:
% 3.75/3.98         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.75/3.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.75/3.98  thf('29', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 3.75/3.98          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 3.75/3.98      inference('sup-', [status(thm)], ['27', '28'])).
% 3.75/3.98  thf('30', plain,
% 3.75/3.98      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 3.75/3.98        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 3.75/3.98      inference('sup-', [status(thm)], ['24', '29'])).
% 3.75/3.98  thf('31', plain,
% 3.75/3.98      (((k1_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('demod', [status(thm)], ['17', '18', '23'])).
% 3.75/3.98  thf('32', plain,
% 3.75/3.98      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 3.75/3.98        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('demod', [status(thm)], ['30', '31'])).
% 3.75/3.98  thf('33', plain,
% 3.75/3.98      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 3.75/3.98         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.75/3.98      inference('sup-', [status(thm)], ['14', '32'])).
% 3.75/3.98  thf('34', plain,
% 3.75/3.98      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf(l78_tops_1, axiom,
% 3.75/3.98    (![A:$i]:
% 3.75/3.98     ( ( l1_pre_topc @ A ) =>
% 3.75/3.98       ( ![B:$i]:
% 3.75/3.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.75/3.98           ( ( k2_tops_1 @ A @ B ) =
% 3.75/3.98             ( k7_subset_1 @
% 3.75/3.98               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 3.75/3.98               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.75/3.98  thf('35', plain,
% 3.75/3.98      (![X48 : $i, X49 : $i]:
% 3.75/3.98         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 3.75/3.98          | ((k2_tops_1 @ X49 @ X48)
% 3.75/3.98              = (k7_subset_1 @ (u1_struct_0 @ X49) @ 
% 3.75/3.98                 (k2_pre_topc @ X49 @ X48) @ (k1_tops_1 @ X49 @ X48)))
% 3.75/3.98          | ~ (l1_pre_topc @ X49))),
% 3.75/3.98      inference('cnf', [status(esa)], [l78_tops_1])).
% 3.75/3.98  thf('36', plain,
% 3.75/3.98      ((~ (l1_pre_topc @ sk_A)
% 3.75/3.98        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 3.75/3.98      inference('sup-', [status(thm)], ['34', '35'])).
% 3.75/3.98  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf('38', plain,
% 3.75/3.98      (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('demod', [status(thm)], ['36', '37'])).
% 3.75/3.98  thf('39', plain,
% 3.75/3.98      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.75/3.98         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.75/3.98      inference('sup+', [status(thm)], ['33', '38'])).
% 3.75/3.98  thf('40', plain,
% 3.75/3.98      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.75/3.98         <= (~
% 3.75/3.98             (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.75/3.98      inference('split', [status(esa)], ['0'])).
% 3.75/3.98  thf('41', plain,
% 3.75/3.98      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 3.75/3.98         <= (~
% 3.75/3.98             (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 3.75/3.98             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.75/3.98      inference('sup-', [status(thm)], ['39', '40'])).
% 3.75/3.98  thf('42', plain,
% 3.75/3.98      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 3.75/3.98       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.75/3.98      inference('simplify', [status(thm)], ['41'])).
% 3.75/3.98  thf('43', plain,
% 3.75/3.98      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 3.75/3.98       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.75/3.98      inference('split', [status(esa)], ['3'])).
% 3.75/3.98  thf('44', plain,
% 3.75/3.98      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf(dt_k2_tops_1, axiom,
% 3.75/3.98    (![A:$i,B:$i]:
% 3.75/3.98     ( ( ( l1_pre_topc @ A ) & 
% 3.75/3.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.75/3.98       ( m1_subset_1 @
% 3.75/3.98         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.75/3.98  thf('45', plain,
% 3.75/3.98      (![X44 : $i, X45 : $i]:
% 3.75/3.98         (~ (l1_pre_topc @ X44)
% 3.75/3.98          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 3.75/3.98          | (m1_subset_1 @ (k2_tops_1 @ X44 @ X45) @ 
% 3.75/3.98             (k1_zfmisc_1 @ (u1_struct_0 @ X44))))),
% 3.75/3.98      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.75/3.98  thf('46', plain,
% 3.75/3.98      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 3.75/3.98         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.75/3.98        | ~ (l1_pre_topc @ sk_A))),
% 3.75/3.98      inference('sup-', [status(thm)], ['44', '45'])).
% 3.75/3.98  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf('48', plain,
% 3.75/3.98      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 3.75/3.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('demod', [status(thm)], ['46', '47'])).
% 3.75/3.98  thf('49', plain,
% 3.75/3.98      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf(dt_k4_subset_1, axiom,
% 3.75/3.98    (![A:$i,B:$i,C:$i]:
% 3.75/3.98     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.75/3.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.75/3.98       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.75/3.98  thf('50', plain,
% 3.75/3.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.75/3.98         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 3.75/3.98          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 3.75/3.98          | (m1_subset_1 @ (k4_subset_1 @ X20 @ X19 @ X21) @ 
% 3.75/3.98             (k1_zfmisc_1 @ X20)))),
% 3.75/3.98      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 3.75/3.98  thf('51', plain,
% 3.75/3.98      (![X0 : $i]:
% 3.75/3.98         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 3.75/3.98           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.75/3.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.75/3.98      inference('sup-', [status(thm)], ['49', '50'])).
% 3.75/3.98  thf('52', plain,
% 3.75/3.98      ((m1_subset_1 @ 
% 3.75/3.98        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.75/3.98         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 3.75/3.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('sup-', [status(thm)], ['48', '51'])).
% 3.75/3.98  thf('53', plain,
% 3.75/3.98      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf(t65_tops_1, axiom,
% 3.75/3.98    (![A:$i]:
% 3.75/3.98     ( ( l1_pre_topc @ A ) =>
% 3.75/3.98       ( ![B:$i]:
% 3.75/3.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.75/3.98           ( ( k2_pre_topc @ A @ B ) =
% 3.75/3.98             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.75/3.98  thf('54', plain,
% 3.75/3.98      (![X53 : $i, X54 : $i]:
% 3.75/3.98         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 3.75/3.98          | ((k2_pre_topc @ X54 @ X53)
% 3.75/3.98              = (k4_subset_1 @ (u1_struct_0 @ X54) @ X53 @ 
% 3.75/3.98                 (k2_tops_1 @ X54 @ X53)))
% 3.75/3.98          | ~ (l1_pre_topc @ X54))),
% 3.75/3.98      inference('cnf', [status(esa)], [t65_tops_1])).
% 3.75/3.98  thf('55', plain,
% 3.75/3.98      ((~ (l1_pre_topc @ sk_A)
% 3.75/3.98        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 3.75/3.98            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.75/3.98               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 3.75/3.98      inference('sup-', [status(thm)], ['53', '54'])).
% 3.75/3.98  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf('57', plain,
% 3.75/3.98      (((k2_pre_topc @ sk_A @ sk_B_1)
% 3.75/3.98         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.75/3.98            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('demod', [status(thm)], ['55', '56'])).
% 3.75/3.98  thf('58', plain,
% 3.75/3.98      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.75/3.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('demod', [status(thm)], ['52', '57'])).
% 3.75/3.98  thf('59', plain,
% 3.75/3.98      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.75/3.98         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 3.75/3.98          | ((k7_subset_1 @ X34 @ X33 @ X35) = (k6_subset_1 @ X33 @ X35)))),
% 3.75/3.98      inference('demod', [status(thm)], ['20', '21'])).
% 3.75/3.98  thf('60', plain,
% 3.75/3.98      (![X0 : $i]:
% 3.75/3.98         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 3.75/3.98           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 3.75/3.98      inference('sup-', [status(thm)], ['58', '59'])).
% 3.75/3.98  thf('61', plain,
% 3.75/3.98      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.75/3.98         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.75/3.98      inference('split', [status(esa)], ['3'])).
% 3.75/3.98  thf('62', plain,
% 3.75/3.98      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.75/3.98         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.75/3.98      inference('sup+', [status(thm)], ['60', '61'])).
% 3.75/3.98  thf('63', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 3.75/3.98      inference('sup-', [status(thm)], ['25', '26'])).
% 3.75/3.98  thf(t28_xboole_1, axiom,
% 3.75/3.98    (![A:$i,B:$i]:
% 3.75/3.98     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.75/3.98  thf('64', plain,
% 3.75/3.98      (![X5 : $i, X6 : $i]:
% 3.75/3.98         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 3.75/3.98      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.75/3.98  thf('65', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         ((k3_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0)
% 3.75/3.98           = (k6_subset_1 @ X0 @ X1))),
% 3.75/3.98      inference('sup-', [status(thm)], ['63', '64'])).
% 3.75/3.98  thf(commutativity_k2_tarski, axiom,
% 3.75/3.98    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.75/3.98  thf('66', plain,
% 3.75/3.98      (![X13 : $i, X14 : $i]:
% 3.75/3.98         ((k2_tarski @ X14 @ X13) = (k2_tarski @ X13 @ X14))),
% 3.75/3.98      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.75/3.98  thf(t12_setfam_1, axiom,
% 3.75/3.98    (![A:$i,B:$i]:
% 3.75/3.98     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.75/3.98  thf('67', plain,
% 3.75/3.98      (![X39 : $i, X40 : $i]:
% 3.75/3.98         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 3.75/3.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.75/3.98  thf('68', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 3.75/3.98      inference('sup+', [status(thm)], ['66', '67'])).
% 3.75/3.98  thf('69', plain,
% 3.75/3.98      (![X39 : $i, X40 : $i]:
% 3.75/3.98         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 3.75/3.98      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.75/3.98  thf('70', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.75/3.98      inference('sup+', [status(thm)], ['68', '69'])).
% 3.75/3.98  thf('71', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         ((k3_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 3.75/3.98           = (k6_subset_1 @ X0 @ X1))),
% 3.75/3.98      inference('demod', [status(thm)], ['65', '70'])).
% 3.75/3.98  thf(t100_xboole_1, axiom,
% 3.75/3.98    (![A:$i,B:$i]:
% 3.75/3.98     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.75/3.98  thf('72', plain,
% 3.75/3.98      (![X3 : $i, X4 : $i]:
% 3.75/3.98         ((k4_xboole_0 @ X3 @ X4)
% 3.75/3.98           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.75/3.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.75/3.98  thf('73', plain,
% 3.75/3.98      (![X31 : $i, X32 : $i]:
% 3.75/3.98         ((k6_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))),
% 3.75/3.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.75/3.98  thf('74', plain,
% 3.75/3.98      (![X3 : $i, X4 : $i]:
% 3.75/3.98         ((k6_subset_1 @ X3 @ X4)
% 3.75/3.98           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 3.75/3.98      inference('demod', [status(thm)], ['72', '73'])).
% 3.75/3.98  thf('75', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         ((k6_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 3.75/3.98           = (k5_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 3.75/3.98      inference('sup+', [status(thm)], ['71', '74'])).
% 3.75/3.98  thf(t48_xboole_1, axiom,
% 3.75/3.98    (![A:$i,B:$i]:
% 3.75/3.98     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.75/3.98  thf('76', plain,
% 3.75/3.98      (![X7 : $i, X8 : $i]:
% 3.75/3.98         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 3.75/3.98           = (k3_xboole_0 @ X7 @ X8))),
% 3.75/3.98      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.75/3.98  thf('77', plain,
% 3.75/3.98      (![X31 : $i, X32 : $i]:
% 3.75/3.98         ((k6_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))),
% 3.75/3.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.75/3.98  thf('78', plain,
% 3.75/3.98      (![X31 : $i, X32 : $i]:
% 3.75/3.98         ((k6_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))),
% 3.75/3.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 3.75/3.98  thf('79', plain,
% 3.75/3.98      (![X7 : $i, X8 : $i]:
% 3.75/3.98         ((k6_subset_1 @ X7 @ (k6_subset_1 @ X7 @ X8))
% 3.75/3.98           = (k3_xboole_0 @ X7 @ X8))),
% 3.75/3.98      inference('demod', [status(thm)], ['76', '77', '78'])).
% 3.75/3.98  thf('80', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         ((k5_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 3.75/3.98           = (k3_xboole_0 @ X1 @ X0))),
% 3.75/3.98      inference('sup+', [status(thm)], ['75', '79'])).
% 3.75/3.98  thf('81', plain,
% 3.75/3.98      ((((k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.75/3.98          (k2_tops_1 @ sk_A @ sk_B_1))
% 3.75/3.98          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 3.75/3.98         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.75/3.98      inference('sup+', [status(thm)], ['62', '80'])).
% 3.75/3.98  thf('82', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.75/3.98      inference('sup+', [status(thm)], ['68', '69'])).
% 3.75/3.98  thf('83', plain,
% 3.75/3.98      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 3.75/3.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('demod', [status(thm)], ['46', '47'])).
% 3.75/3.98  thf('84', plain,
% 3.75/3.98      (![X41 : $i, X42 : $i]:
% 3.75/3.98         ((r1_tarski @ X41 @ X42) | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 3.75/3.98      inference('cnf', [status(esa)], [t3_subset])).
% 3.75/3.98  thf('85', plain,
% 3.75/3.98      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 3.75/3.98      inference('sup-', [status(thm)], ['83', '84'])).
% 3.75/3.98  thf('86', plain,
% 3.75/3.98      (![X5 : $i, X6 : $i]:
% 3.75/3.98         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 3.75/3.98      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.75/3.98  thf('87', plain,
% 3.75/3.98      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 3.75/3.98         = (k2_tops_1 @ sk_A @ sk_B_1))),
% 3.75/3.98      inference('sup-', [status(thm)], ['85', '86'])).
% 3.75/3.98  thf('88', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.75/3.98      inference('sup+', [status(thm)], ['68', '69'])).
% 3.75/3.98  thf('89', plain,
% 3.75/3.98      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))
% 3.75/3.98         = (k2_tops_1 @ sk_A @ sk_B_1))),
% 3.75/3.98      inference('demod', [status(thm)], ['87', '88'])).
% 3.75/3.98  thf('90', plain,
% 3.75/3.98      (![X7 : $i, X8 : $i]:
% 3.75/3.98         ((k6_subset_1 @ X7 @ (k6_subset_1 @ X7 @ X8))
% 3.75/3.98           = (k3_xboole_0 @ X7 @ X8))),
% 3.75/3.98      inference('demod', [status(thm)], ['76', '77', '78'])).
% 3.75/3.98  thf('91', plain,
% 3.75/3.98      (![X22 : $i, X23 : $i]:
% 3.75/3.98         (m1_subset_1 @ (k6_subset_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))),
% 3.75/3.98      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 3.75/3.98  thf('92', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 3.75/3.98      inference('sup+', [status(thm)], ['90', '91'])).
% 3.75/3.98  thf('93', plain,
% 3.75/3.98      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf(redefinition_k4_subset_1, axiom,
% 3.75/3.98    (![A:$i,B:$i,C:$i]:
% 3.75/3.98     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.75/3.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.75/3.98       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.75/3.98  thf('94', plain,
% 3.75/3.98      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.75/3.98         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 3.75/3.98          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 3.75/3.98          | ((k4_subset_1 @ X29 @ X28 @ X30) = (k2_xboole_0 @ X28 @ X30)))),
% 3.75/3.98      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.75/3.98  thf('95', plain,
% 3.75/3.98      (![X0 : $i]:
% 3.75/3.98         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 3.75/3.98            = (k2_xboole_0 @ sk_B_1 @ X0))
% 3.75/3.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.75/3.98      inference('sup-', [status(thm)], ['93', '94'])).
% 3.75/3.98  thf('96', plain,
% 3.75/3.98      (![X0 : $i]:
% 3.75/3.98         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.75/3.98           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 3.75/3.98           = (k2_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 3.75/3.98      inference('sup-', [status(thm)], ['92', '95'])).
% 3.75/3.98  thf('97', plain,
% 3.75/3.98      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.75/3.98         (k2_tops_1 @ sk_A @ sk_B_1))
% 3.75/3.98         = (k2_xboole_0 @ sk_B_1 @ 
% 3.75/3.98            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 3.75/3.98      inference('sup+', [status(thm)], ['89', '96'])).
% 3.75/3.98  thf('98', plain,
% 3.75/3.98      (((k2_pre_topc @ sk_A @ sk_B_1)
% 3.75/3.98         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 3.75/3.98            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('demod', [status(thm)], ['55', '56'])).
% 3.75/3.98  thf('99', plain,
% 3.75/3.98      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))
% 3.75/3.98         = (k2_tops_1 @ sk_A @ sk_B_1))),
% 3.75/3.98      inference('demod', [status(thm)], ['87', '88'])).
% 3.75/3.98  thf('100', plain,
% 3.75/3.98      (((k2_pre_topc @ sk_A @ sk_B_1)
% 3.75/3.98         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('demod', [status(thm)], ['97', '98', '99'])).
% 3.75/3.98  thf(t7_xboole_1, axiom,
% 3.75/3.98    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.75/3.98  thf('101', plain,
% 3.75/3.98      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 3.75/3.98      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.75/3.98  thf('102', plain,
% 3.75/3.98      (![X5 : $i, X6 : $i]:
% 3.75/3.98         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 3.75/3.98      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.75/3.98  thf('103', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 3.75/3.98      inference('sup-', [status(thm)], ['101', '102'])).
% 3.75/3.98  thf('104', plain,
% 3.75/3.98      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 3.75/3.98      inference('sup+', [status(thm)], ['100', '103'])).
% 3.75/3.98  thf('105', plain,
% 3.75/3.98      ((((k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.75/3.98          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 3.75/3.98         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.75/3.98      inference('demod', [status(thm)], ['81', '82', '104'])).
% 3.75/3.98  thf('106', plain,
% 3.75/3.98      (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('demod', [status(thm)], ['36', '37'])).
% 3.75/3.98  thf('107', plain,
% 3.75/3.98      (![X0 : $i]:
% 3.75/3.98         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 3.75/3.98           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 3.75/3.98      inference('sup-', [status(thm)], ['58', '59'])).
% 3.75/3.98  thf('108', plain,
% 3.75/3.98      (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.75/3.98            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('demod', [status(thm)], ['106', '107'])).
% 3.75/3.98  thf('109', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         ((k5_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 3.75/3.98           = (k3_xboole_0 @ X1 @ X0))),
% 3.75/3.98      inference('sup+', [status(thm)], ['75', '79'])).
% 3.75/3.98  thf('110', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.75/3.98      inference('sup+', [status(thm)], ['68', '69'])).
% 3.75/3.98  thf('111', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 3.75/3.98      inference('sup+', [status(thm)], ['90', '91'])).
% 3.75/3.98  thf('112', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 3.75/3.98      inference('sup+', [status(thm)], ['110', '111'])).
% 3.75/3.98  thf('113', plain,
% 3.75/3.98      (![X0 : $i, X1 : $i]:
% 3.75/3.98         (m1_subset_1 @ (k5_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)) @ 
% 3.75/3.98          (k1_zfmisc_1 @ X0))),
% 3.75/3.98      inference('sup+', [status(thm)], ['109', '112'])).
% 3.75/3.98  thf('114', plain,
% 3.75/3.98      ((m1_subset_1 @ 
% 3.75/3.98        (k5_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 3.75/3.98         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 3.75/3.98        (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('sup+', [status(thm)], ['108', '113'])).
% 3.75/3.98  thf('115', plain,
% 3.75/3.98      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 3.75/3.98         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.75/3.98      inference('sup+', [status(thm)], ['105', '114'])).
% 3.75/3.98  thf('116', plain,
% 3.75/3.98      (![X41 : $i, X42 : $i]:
% 3.75/3.98         ((r1_tarski @ X41 @ X42) | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 3.75/3.98      inference('cnf', [status(esa)], [t3_subset])).
% 3.75/3.98  thf('117', plain,
% 3.75/3.98      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 3.75/3.98         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.75/3.98      inference('sup-', [status(thm)], ['115', '116'])).
% 3.75/3.98  thf('118', plain,
% 3.75/3.98      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 3.75/3.98        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 3.75/3.98      inference('demod', [status(thm)], ['30', '31'])).
% 3.75/3.98  thf('119', plain,
% 3.75/3.98      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 3.75/3.98         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.75/3.98      inference('sup-', [status(thm)], ['117', '118'])).
% 3.75/3.98  thf('120', plain,
% 3.75/3.98      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf(fc9_tops_1, axiom,
% 3.75/3.98    (![A:$i,B:$i]:
% 3.75/3.98     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 3.75/3.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.75/3.98       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 3.75/3.98  thf('121', plain,
% 3.75/3.98      (![X46 : $i, X47 : $i]:
% 3.75/3.98         (~ (l1_pre_topc @ X46)
% 3.75/3.98          | ~ (v2_pre_topc @ X46)
% 3.75/3.98          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 3.75/3.98          | (v3_pre_topc @ (k1_tops_1 @ X46 @ X47) @ X46))),
% 3.75/3.98      inference('cnf', [status(esa)], [fc9_tops_1])).
% 3.75/3.98  thf('122', plain,
% 3.75/3.98      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 3.75/3.98        | ~ (v2_pre_topc @ sk_A)
% 3.75/3.98        | ~ (l1_pre_topc @ sk_A))),
% 3.75/3.98      inference('sup-', [status(thm)], ['120', '121'])).
% 3.75/3.98  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 3.75/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.75/3.98  thf('125', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 3.75/3.98      inference('demod', [status(thm)], ['122', '123', '124'])).
% 3.75/3.98  thf('126', plain,
% 3.75/3.98      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 3.75/3.98         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 3.75/3.98      inference('sup+', [status(thm)], ['119', '125'])).
% 3.75/3.98  thf('127', plain,
% 3.75/3.98      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 3.75/3.98      inference('split', [status(esa)], ['0'])).
% 3.75/3.98  thf('128', plain,
% 3.75/3.98      (~
% 3.75/3.98       (((k2_tops_1 @ sk_A @ sk_B_1)
% 3.75/3.98          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.75/3.98             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 3.75/3.98       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 3.75/3.98      inference('sup-', [status(thm)], ['126', '127'])).
% 3.75/3.98  thf('129', plain, ($false),
% 3.75/3.98      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '128'])).
% 3.75/3.98  
% 3.75/3.98  % SZS output end Refutation
% 3.75/3.98  
% 3.75/3.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
