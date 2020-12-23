%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tXPjMXA2RU

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:25 EST 2020

% Result     : Theorem 12.90s
% Output     : Refutation 12.90s
% Verified   : 
% Statistics : Number of formulae       :  269 (1769 expanded)
%              Number of leaves         :   53 ( 595 expanded)
%              Depth                    :   23
%              Number of atoms          : 2267 (15504 expanded)
%              Number of equality atoms :  159 (1365 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ~ ( v3_pre_topc @ X66 @ X67 )
      | ~ ( r1_tarski @ X66 @ X68 )
      | ( r1_tarski @ X66 @ ( k1_tops_1 @ X67 @ X68 ) )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ~ ( l1_pre_topc @ X67 ) ) ),
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
    ! [X73: $i,X74: $i] :
      ( ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X74 ) ) )
      | ( ( k1_tops_1 @ X74 @ X73 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X74 ) @ X73 @ ( k2_tops_1 @ X74 @ X73 ) ) )
      | ~ ( l1_pre_topc @ X74 ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ( ( k7_subset_1 @ X50 @ X49 @ X51 )
        = ( k4_xboole_0 @ X49 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ( ( k7_subset_1 @ X50 @ X49 @ X51 )
        = ( k6_subset_1 @ X49 @ X51 ) ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X57: $i,X58: $i] :
      ( ( r1_tarski @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ X58 ) ) ) ),
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
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ( ( k2_tops_1 @ X65 @ X64 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X65 ) @ ( k2_pre_topc @ X65 @ X64 ) @ ( k1_tops_1 @ X65 @ X64 ) ) )
      | ~ ( l1_pre_topc @ X65 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
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
    ! [X60: $i,X61: $i] :
      ( ~ ( l1_pre_topc @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X60 @ X61 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) ) ) ),
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
    ! [X57: $i,X58: $i] :
      ( ( r1_tarski @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ X58 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('56',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('57',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('59',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('60',plain,
    ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('62',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('63',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('64',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k6_subset_1 @ X19 @ X20 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('66',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k6_subset_1 @ X24 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('69',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('74',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','73','74'])).

thf('76',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','75'])).

thf('77',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('78',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X55 @ X56 ) )
      = ( k3_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X55 @ X56 ) )
      = ( k3_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('82',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('83',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('84',plain,(
    ! [X14: $i] :
      ( ( k6_subset_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k6_subset_1 @ X24 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('96',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X14: $i] :
      ( ( k6_subset_1 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['93','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['86','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('106',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k6_subset_1 @ X24 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['103','110'])).

thf('112',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['76','81','111'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('113',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('114',plain,(
    ! [X57: $i,X59: $i] :
      ( ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ X59 ) )
      | ~ ( r1_tarski @ X57 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('117',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k4_subset_1 @ X45 @ X44 @ X46 )
        = ( k2_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['112','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('122',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( m1_subset_1 @ X71 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X72 ) ) )
      | ( ( k2_pre_topc @ X72 @ X71 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X72 ) @ X71 @ ( k2_tops_1 @ X72 @ X71 ) ) )
      | ~ ( l1_pre_topc @ X72 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('123',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['76','81','111'])).

thf('127',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['120','125','126'])).

thf('128',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('129',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','23'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('132',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['129','134'])).

thf('136',plain,(
    ! [X57: $i,X59: $i] :
      ( ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ X59 ) )
      | ~ ( r1_tarski @ X57 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('137',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('138',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k3_subset_1 @ X43 @ ( k3_subset_1 @ X43 @ X42 ) )
        = X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('139',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('141',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('142',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('143',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k6_subset_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('146',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('147',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('148',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X34 @ X33 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('152',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) )
      | ( ( k7_subset_1 @ X50 @ X49 @ X51 )
        = ( k6_subset_1 @ X49 @ X51 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['145','154'])).

thf('156',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['144','155'])).

thf('157',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['139','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('159',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('160',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k6_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('162',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k3_subset_1 @ X43 @ ( k3_subset_1 @ X43 @ X42 ) )
        = X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('165',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k6_subset_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k6_subset_1 @ X19 @ X20 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['163','168'])).

thf('170',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['160','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('172',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['120','125','126'])).

thf('173',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('174',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('175',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['172','177'])).

thf('179',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('180',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('182',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k6_subset_1 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','73','74'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('190',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['103','110'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['188','191'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('193',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('194',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k6_subset_1 @ X47 @ X48 )
      = ( k4_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('195',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k6_subset_1 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['192','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['187','196'])).

thf('198',plain,
    ( ( k6_subset_1 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['180','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','73','74'])).

thf('200',plain,
    ( sk_B_1
    = ( k5_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['198','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['103','110'])).

thf('202',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['170','171','202'])).

thf('204',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['157','203'])).

thf('205',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('206',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( l1_pre_topc @ X62 )
      | ~ ( v2_pre_topc @ X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X62 @ X63 ) @ X62 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('207',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['204','210'])).

thf('212',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('213',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','42','43','213'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tXPjMXA2RU
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:16:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 12.90/13.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.90/13.10  % Solved by: fo/fo7.sh
% 12.90/13.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.90/13.10  % done 22839 iterations in 12.639s
% 12.90/13.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.90/13.10  % SZS output start Refutation
% 12.90/13.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 12.90/13.10  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 12.90/13.10  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 12.90/13.10  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 12.90/13.10  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 12.90/13.10  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 12.90/13.10  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 12.90/13.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.90/13.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 12.90/13.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.90/13.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.90/13.10  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 12.90/13.10  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 12.90/13.10  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 12.90/13.10  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 12.90/13.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.90/13.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.90/13.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.90/13.10  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 12.90/13.10  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 12.90/13.10  thf(sk_A_type, type, sk_A: $i).
% 12.90/13.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 12.90/13.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 12.90/13.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 12.90/13.10  thf(t76_tops_1, conjecture,
% 12.90/13.10    (![A:$i]:
% 12.90/13.10     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.90/13.10       ( ![B:$i]:
% 12.90/13.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.90/13.10           ( ( v3_pre_topc @ B @ A ) <=>
% 12.90/13.10             ( ( k2_tops_1 @ A @ B ) =
% 12.90/13.10               ( k7_subset_1 @
% 12.90/13.10                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 12.90/13.10  thf(zf_stmt_0, negated_conjecture,
% 12.90/13.10    (~( ![A:$i]:
% 12.90/13.10        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.90/13.10          ( ![B:$i]:
% 12.90/13.10            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.90/13.10              ( ( v3_pre_topc @ B @ A ) <=>
% 12.90/13.10                ( ( k2_tops_1 @ A @ B ) =
% 12.90/13.10                  ( k7_subset_1 @
% 12.90/13.10                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 12.90/13.10    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 12.90/13.10  thf('0', plain,
% 12.90/13.10      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 12.90/13.10        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf('1', plain,
% 12.90/13.10      (~
% 12.90/13.10       (((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 12.90/13.10       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 12.90/13.10      inference('split', [status(esa)], ['0'])).
% 12.90/13.10  thf('2', plain,
% 12.90/13.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf('3', plain,
% 12.90/13.10      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 12.90/13.10        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf('4', plain,
% 12.90/13.10      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 12.90/13.10      inference('split', [status(esa)], ['3'])).
% 12.90/13.10  thf('5', plain,
% 12.90/13.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf(t56_tops_1, axiom,
% 12.90/13.10    (![A:$i]:
% 12.90/13.10     ( ( l1_pre_topc @ A ) =>
% 12.90/13.10       ( ![B:$i]:
% 12.90/13.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.90/13.10           ( ![C:$i]:
% 12.90/13.10             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.90/13.10               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 12.90/13.10                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 12.90/13.10  thf('6', plain,
% 12.90/13.10      (![X66 : $i, X67 : $i, X68 : $i]:
% 12.90/13.10         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 12.90/13.10          | ~ (v3_pre_topc @ X66 @ X67)
% 12.90/13.10          | ~ (r1_tarski @ X66 @ X68)
% 12.90/13.10          | (r1_tarski @ X66 @ (k1_tops_1 @ X67 @ X68))
% 12.90/13.10          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 12.90/13.10          | ~ (l1_pre_topc @ X67))),
% 12.90/13.10      inference('cnf', [status(esa)], [t56_tops_1])).
% 12.90/13.10  thf('7', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         (~ (l1_pre_topc @ sk_A)
% 12.90/13.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.10          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 12.90/13.10          | ~ (r1_tarski @ sk_B_1 @ X0)
% 12.90/13.10          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 12.90/13.10      inference('sup-', [status(thm)], ['5', '6'])).
% 12.90/13.10  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf('9', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.10          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 12.90/13.10          | ~ (r1_tarski @ sk_B_1 @ X0)
% 12.90/13.10          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 12.90/13.10      inference('demod', [status(thm)], ['7', '8'])).
% 12.90/13.10  thf('10', plain,
% 12.90/13.10      ((![X0 : $i]:
% 12.90/13.10          (~ (r1_tarski @ sk_B_1 @ X0)
% 12.90/13.10           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 12.90/13.10           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 12.90/13.10         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['4', '9'])).
% 12.90/13.10  thf('11', plain,
% 12.90/13.10      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 12.90/13.10         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 12.90/13.10         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['2', '10'])).
% 12.90/13.10  thf(d10_xboole_0, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 12.90/13.10  thf('12', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 12.90/13.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.90/13.10  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 12.90/13.10      inference('simplify', [status(thm)], ['12'])).
% 12.90/13.10  thf('14', plain,
% 12.90/13.10      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 12.90/13.10         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 12.90/13.10      inference('demod', [status(thm)], ['11', '13'])).
% 12.90/13.10  thf('15', plain,
% 12.90/13.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf(t74_tops_1, axiom,
% 12.90/13.10    (![A:$i]:
% 12.90/13.10     ( ( l1_pre_topc @ A ) =>
% 12.90/13.10       ( ![B:$i]:
% 12.90/13.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.90/13.10           ( ( k1_tops_1 @ A @ B ) =
% 12.90/13.10             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 12.90/13.10  thf('16', plain,
% 12.90/13.10      (![X73 : $i, X74 : $i]:
% 12.90/13.10         (~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (u1_struct_0 @ X74)))
% 12.90/13.10          | ((k1_tops_1 @ X74 @ X73)
% 12.90/13.10              = (k7_subset_1 @ (u1_struct_0 @ X74) @ X73 @ 
% 12.90/13.10                 (k2_tops_1 @ X74 @ X73)))
% 12.90/13.10          | ~ (l1_pre_topc @ X74))),
% 12.90/13.10      inference('cnf', [status(esa)], [t74_tops_1])).
% 12.90/13.10  thf('17', plain,
% 12.90/13.10      ((~ (l1_pre_topc @ sk_A)
% 12.90/13.10        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 12.90/13.10               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 12.90/13.10      inference('sup-', [status(thm)], ['15', '16'])).
% 12.90/13.10  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf('19', plain,
% 12.90/13.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf(redefinition_k7_subset_1, axiom,
% 12.90/13.10    (![A:$i,B:$i,C:$i]:
% 12.90/13.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 12.90/13.10       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 12.90/13.10  thf('20', plain,
% 12.90/13.10      (![X49 : $i, X50 : $i, X51 : $i]:
% 12.90/13.10         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 12.90/13.10          | ((k7_subset_1 @ X50 @ X49 @ X51) = (k4_xboole_0 @ X49 @ X51)))),
% 12.90/13.10      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 12.90/13.10  thf(redefinition_k6_subset_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 12.90/13.10  thf('21', plain,
% 12.90/13.10      (![X47 : $i, X48 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 12.90/13.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.90/13.10  thf('22', plain,
% 12.90/13.10      (![X49 : $i, X50 : $i, X51 : $i]:
% 12.90/13.10         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 12.90/13.10          | ((k7_subset_1 @ X50 @ X49 @ X51) = (k6_subset_1 @ X49 @ X51)))),
% 12.90/13.10      inference('demod', [status(thm)], ['20', '21'])).
% 12.90/13.10  thf('23', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 12.90/13.10           = (k6_subset_1 @ sk_B_1 @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['19', '22'])).
% 12.90/13.10  thf('24', plain,
% 12.90/13.10      (((k1_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['17', '18', '23'])).
% 12.90/13.10  thf(dt_k6_subset_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 12.90/13.10  thf('25', plain,
% 12.90/13.10      (![X36 : $i, X37 : $i]:
% 12.90/13.10         (m1_subset_1 @ (k6_subset_1 @ X36 @ X37) @ (k1_zfmisc_1 @ X36))),
% 12.90/13.10      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 12.90/13.10  thf(t3_subset, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 12.90/13.10  thf('26', plain,
% 12.90/13.10      (![X57 : $i, X58 : $i]:
% 12.90/13.10         ((r1_tarski @ X57 @ X58) | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ X58)))),
% 12.90/13.10      inference('cnf', [status(esa)], [t3_subset])).
% 12.90/13.10  thf('27', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 12.90/13.10      inference('sup-', [status(thm)], ['25', '26'])).
% 12.90/13.10  thf('28', plain,
% 12.90/13.10      (![X0 : $i, X2 : $i]:
% 12.90/13.10         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 12.90/13.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.90/13.10  thf('29', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         (~ (r1_tarski @ X0 @ (k6_subset_1 @ X0 @ X1))
% 12.90/13.10          | ((X0) = (k6_subset_1 @ X0 @ X1)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['27', '28'])).
% 12.90/13.10  thf('30', plain,
% 12.90/13.10      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 12.90/13.10        | ((sk_B_1) = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 12.90/13.10      inference('sup-', [status(thm)], ['24', '29'])).
% 12.90/13.10  thf('31', plain,
% 12.90/13.10      (((k1_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['17', '18', '23'])).
% 12.90/13.10  thf('32', plain,
% 12.90/13.10      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 12.90/13.10        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['30', '31'])).
% 12.90/13.10  thf('33', plain,
% 12.90/13.10      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 12.90/13.10         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['14', '32'])).
% 12.90/13.10  thf('34', plain,
% 12.90/13.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf(l78_tops_1, axiom,
% 12.90/13.10    (![A:$i]:
% 12.90/13.10     ( ( l1_pre_topc @ A ) =>
% 12.90/13.10       ( ![B:$i]:
% 12.90/13.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.90/13.10           ( ( k2_tops_1 @ A @ B ) =
% 12.90/13.10             ( k7_subset_1 @
% 12.90/13.10               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 12.90/13.10               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 12.90/13.10  thf('35', plain,
% 12.90/13.10      (![X64 : $i, X65 : $i]:
% 12.90/13.10         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 12.90/13.10          | ((k2_tops_1 @ X65 @ X64)
% 12.90/13.10              = (k7_subset_1 @ (u1_struct_0 @ X65) @ 
% 12.90/13.10                 (k2_pre_topc @ X65 @ X64) @ (k1_tops_1 @ X65 @ X64)))
% 12.90/13.10          | ~ (l1_pre_topc @ X65))),
% 12.90/13.10      inference('cnf', [status(esa)], [l78_tops_1])).
% 12.90/13.10  thf('36', plain,
% 12.90/13.10      ((~ (l1_pre_topc @ sk_A)
% 12.90/13.10        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 12.90/13.10      inference('sup-', [status(thm)], ['34', '35'])).
% 12.90/13.10  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf('38', plain,
% 12.90/13.10      (((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['36', '37'])).
% 12.90/13.10  thf('39', plain,
% 12.90/13.10      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 12.90/13.10         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 12.90/13.10      inference('sup+', [status(thm)], ['33', '38'])).
% 12.90/13.10  thf('40', plain,
% 12.90/13.10      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 12.90/13.10         <= (~
% 12.90/13.10             (((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 12.90/13.10      inference('split', [status(esa)], ['0'])).
% 12.90/13.10  thf('41', plain,
% 12.90/13.10      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 12.90/13.10         <= (~
% 12.90/13.10             (((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 12.90/13.10             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['39', '40'])).
% 12.90/13.10  thf('42', plain,
% 12.90/13.10      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 12.90/13.10       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 12.90/13.10      inference('simplify', [status(thm)], ['41'])).
% 12.90/13.10  thf('43', plain,
% 12.90/13.10      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 12.90/13.10       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 12.90/13.10      inference('split', [status(esa)], ['3'])).
% 12.90/13.10  thf(t7_xboole_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 12.90/13.10  thf('44', plain,
% 12.90/13.10      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 12.90/13.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.90/13.10  thf('45', plain,
% 12.90/13.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf(dt_k2_tops_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( ( l1_pre_topc @ A ) & 
% 12.90/13.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 12.90/13.10       ( m1_subset_1 @
% 12.90/13.10         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 12.90/13.10  thf('46', plain,
% 12.90/13.10      (![X60 : $i, X61 : $i]:
% 12.90/13.10         (~ (l1_pre_topc @ X60)
% 12.90/13.10          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 12.90/13.10          | (m1_subset_1 @ (k2_tops_1 @ X60 @ X61) @ 
% 12.90/13.10             (k1_zfmisc_1 @ (u1_struct_0 @ X60))))),
% 12.90/13.10      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 12.90/13.10  thf('47', plain,
% 12.90/13.10      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 12.90/13.10         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.10        | ~ (l1_pre_topc @ sk_A))),
% 12.90/13.10      inference('sup-', [status(thm)], ['45', '46'])).
% 12.90/13.10  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf('49', plain,
% 12.90/13.10      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 12.90/13.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('demod', [status(thm)], ['47', '48'])).
% 12.90/13.10  thf('50', plain,
% 12.90/13.10      (![X57 : $i, X58 : $i]:
% 12.90/13.10         ((r1_tarski @ X57 @ X58) | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ X58)))),
% 12.90/13.10      inference('cnf', [status(esa)], [t3_subset])).
% 12.90/13.10  thf('51', plain,
% 12.90/13.10      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 12.90/13.10      inference('sup-', [status(thm)], ['49', '50'])).
% 12.90/13.10  thf(t1_xboole_1, axiom,
% 12.90/13.10    (![A:$i,B:$i,C:$i]:
% 12.90/13.10     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 12.90/13.10       ( r1_tarski @ A @ C ) ))).
% 12.90/13.10  thf('52', plain,
% 12.90/13.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 12.90/13.10         (~ (r1_tarski @ X7 @ X8)
% 12.90/13.10          | ~ (r1_tarski @ X8 @ X9)
% 12.90/13.10          | (r1_tarski @ X7 @ X9))),
% 12.90/13.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 12.90/13.10  thf('53', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ X0)
% 12.90/13.10          | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['51', '52'])).
% 12.90/13.10  thf('54', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 12.90/13.10          (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['44', '53'])).
% 12.90/13.10  thf(t43_xboole_1, axiom,
% 12.90/13.10    (![A:$i,B:$i,C:$i]:
% 12.90/13.10     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 12.90/13.10       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 12.90/13.10  thf('55', plain,
% 12.90/13.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.10         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 12.90/13.10          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 12.90/13.10      inference('cnf', [status(esa)], [t43_xboole_1])).
% 12.90/13.10  thf('56', plain,
% 12.90/13.10      (![X47 : $i, X48 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 12.90/13.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.90/13.10  thf('57', plain,
% 12.90/13.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.10         ((r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18)
% 12.90/13.10          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 12.90/13.10      inference('demod', [status(thm)], ['55', '56'])).
% 12.90/13.10  thf('58', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         (r1_tarski @ 
% 12.90/13.10          (k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)) @ 
% 12.90/13.10          X0)),
% 12.90/13.10      inference('sup-', [status(thm)], ['54', '57'])).
% 12.90/13.10  thf(t3_xboole_1, axiom,
% 12.90/13.10    (![A:$i]:
% 12.90/13.10     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 12.90/13.10  thf('59', plain,
% 12.90/13.10      (![X15 : $i]:
% 12.90/13.10         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 12.90/13.10      inference('cnf', [status(esa)], [t3_xboole_1])).
% 12.90/13.10  thf('60', plain,
% 12.90/13.10      (((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 12.90/13.10         = (k1_xboole_0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['58', '59'])).
% 12.90/13.10  thf(t47_xboole_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 12.90/13.10  thf('61', plain,
% 12.90/13.10      (![X19 : $i, X20 : $i]:
% 12.90/13.10         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 12.90/13.10           = (k4_xboole_0 @ X19 @ X20))),
% 12.90/13.10      inference('cnf', [status(esa)], [t47_xboole_1])).
% 12.90/13.10  thf('62', plain,
% 12.90/13.10      (![X47 : $i, X48 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 12.90/13.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.90/13.10  thf('63', plain,
% 12.90/13.10      (![X47 : $i, X48 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 12.90/13.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.90/13.10  thf('64', plain,
% 12.90/13.10      (![X19 : $i, X20 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 12.90/13.10           = (k6_subset_1 @ X19 @ X20))),
% 12.90/13.10      inference('demod', [status(thm)], ['61', '62', '63'])).
% 12.90/13.10  thf(t98_xboole_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 12.90/13.10  thf('65', plain,
% 12.90/13.10      (![X23 : $i, X24 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ X23 @ X24)
% 12.90/13.10           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 12.90/13.10      inference('cnf', [status(esa)], [t98_xboole_1])).
% 12.90/13.10  thf('66', plain,
% 12.90/13.10      (![X47 : $i, X48 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 12.90/13.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.90/13.10  thf('67', plain,
% 12.90/13.10      (![X23 : $i, X24 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ X23 @ X24)
% 12.90/13.10           = (k5_xboole_0 @ X23 @ (k6_subset_1 @ X24 @ X23)))),
% 12.90/13.10      inference('demod', [status(thm)], ['65', '66'])).
% 12.90/13.10  thf('68', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 12.90/13.10           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 12.90/13.10      inference('sup+', [status(thm)], ['64', '67'])).
% 12.90/13.10  thf(commutativity_k2_tarski, axiom,
% 12.90/13.10    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 12.90/13.10  thf('69', plain,
% 12.90/13.10      (![X25 : $i, X26 : $i]:
% 12.90/13.10         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 12.90/13.10      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 12.90/13.10  thf(l51_zfmisc_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 12.90/13.10  thf('70', plain,
% 12.90/13.10      (![X27 : $i, X28 : $i]:
% 12.90/13.10         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 12.90/13.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 12.90/13.10  thf('71', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 12.90/13.10      inference('sup+', [status(thm)], ['69', '70'])).
% 12.90/13.10  thf('72', plain,
% 12.90/13.10      (![X27 : $i, X28 : $i]:
% 12.90/13.10         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 12.90/13.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 12.90/13.10  thf('73', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.90/13.10      inference('sup+', [status(thm)], ['71', '72'])).
% 12.90/13.10  thf(t22_xboole_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 12.90/13.10  thf('74', plain,
% 12.90/13.10      (![X10 : $i, X11 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)) = (X10))),
% 12.90/13.10      inference('cnf', [status(esa)], [t22_xboole_1])).
% 12.90/13.10  thf('75', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((X1)
% 12.90/13.10           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 12.90/13.10      inference('demod', [status(thm)], ['68', '73', '74'])).
% 12.90/13.10  thf('76', plain,
% 12.90/13.10      (((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10         = (k5_xboole_0 @ 
% 12.90/13.10            (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A)) @ 
% 12.90/13.10            k1_xboole_0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['60', '75'])).
% 12.90/13.10  thf('77', plain,
% 12.90/13.10      (![X25 : $i, X26 : $i]:
% 12.90/13.10         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 12.90/13.10      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 12.90/13.10  thf(t12_setfam_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 12.90/13.10  thf('78', plain,
% 12.90/13.10      (![X55 : $i, X56 : $i]:
% 12.90/13.10         ((k1_setfam_1 @ (k2_tarski @ X55 @ X56)) = (k3_xboole_0 @ X55 @ X56))),
% 12.90/13.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 12.90/13.10  thf('79', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 12.90/13.10      inference('sup+', [status(thm)], ['77', '78'])).
% 12.90/13.10  thf('80', plain,
% 12.90/13.10      (![X55 : $i, X56 : $i]:
% 12.90/13.10         ((k1_setfam_1 @ (k2_tarski @ X55 @ X56)) = (k3_xboole_0 @ X55 @ X56))),
% 12.90/13.10      inference('cnf', [status(esa)], [t12_setfam_1])).
% 12.90/13.10  thf('81', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.90/13.10      inference('sup+', [status(thm)], ['79', '80'])).
% 12.90/13.10  thf(t3_boole, axiom,
% 12.90/13.10    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 12.90/13.10  thf('82', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 12.90/13.10      inference('cnf', [status(esa)], [t3_boole])).
% 12.90/13.10  thf('83', plain,
% 12.90/13.10      (![X47 : $i, X48 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 12.90/13.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.90/13.10  thf('84', plain, (![X14 : $i]: ((k6_subset_1 @ X14 @ k1_xboole_0) = (X14))),
% 12.90/13.10      inference('demod', [status(thm)], ['82', '83'])).
% 12.90/13.10  thf('85', plain,
% 12.90/13.10      (![X23 : $i, X24 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ X23 @ X24)
% 12.90/13.10           = (k5_xboole_0 @ X23 @ (k6_subset_1 @ X24 @ X23)))),
% 12.90/13.10      inference('demod', [status(thm)], ['65', '66'])).
% 12.90/13.10  thf('86', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['84', '85'])).
% 12.90/13.10  thf('87', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.90/13.10      inference('sup+', [status(thm)], ['71', '72'])).
% 12.90/13.10  thf('88', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['84', '85'])).
% 12.90/13.10  thf('89', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['87', '88'])).
% 12.90/13.10  thf('90', plain,
% 12.90/13.10      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 12.90/13.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.90/13.10  thf('91', plain,
% 12.90/13.10      (![X0 : $i, X2 : $i]:
% 12.90/13.10         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 12.90/13.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.90/13.10  thf('92', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 12.90/13.10          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['90', '91'])).
% 12.90/13.10  thf('93', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         (~ (r1_tarski @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0)
% 12.90/13.10          | ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['89', '92'])).
% 12.90/13.10  thf('94', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 12.90/13.10      inference('simplify', [status(thm)], ['12'])).
% 12.90/13.10  thf('95', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['84', '85'])).
% 12.90/13.10  thf('96', plain,
% 12.90/13.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.10         ((r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18)
% 12.90/13.10          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 12.90/13.10      inference('demod', [status(thm)], ['55', '56'])).
% 12.90/13.10  thf('97', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 12.90/13.10          | (r1_tarski @ (k6_subset_1 @ X1 @ k1_xboole_0) @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['95', '96'])).
% 12.90/13.10  thf('98', plain, (![X14 : $i]: ((k6_subset_1 @ X14 @ k1_xboole_0) = (X14))),
% 12.90/13.10      inference('demod', [status(thm)], ['82', '83'])).
% 12.90/13.10  thf('99', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 12.90/13.10          | (r1_tarski @ X1 @ X0))),
% 12.90/13.10      inference('demod', [status(thm)], ['97', '98'])).
% 12.90/13.10  thf('100', plain,
% 12.90/13.10      (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 12.90/13.10      inference('sup-', [status(thm)], ['94', '99'])).
% 12.90/13.10  thf('101', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['87', '88'])).
% 12.90/13.10  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 12.90/13.10      inference('demod', [status(thm)], ['93', '100', '101'])).
% 12.90/13.10  thf('103', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 12.90/13.10      inference('demod', [status(thm)], ['86', '102'])).
% 12.90/13.10  thf('104', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 12.90/13.10      inference('sup+', [status(thm)], ['71', '72'])).
% 12.90/13.10  thf('105', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 12.90/13.10      inference('sup-', [status(thm)], ['25', '26'])).
% 12.90/13.10  thf('106', plain,
% 12.90/13.10      (![X15 : $i]:
% 12.90/13.10         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 12.90/13.10      inference('cnf', [status(esa)], [t3_xboole_1])).
% 12.90/13.10  thf('107', plain,
% 12.90/13.10      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['105', '106'])).
% 12.90/13.10  thf('108', plain,
% 12.90/13.10      (![X23 : $i, X24 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ X23 @ X24)
% 12.90/13.10           = (k5_xboole_0 @ X23 @ (k6_subset_1 @ X24 @ X23)))),
% 12.90/13.10      inference('demod', [status(thm)], ['65', '66'])).
% 12.90/13.10  thf('109', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['107', '108'])).
% 12.90/13.10  thf('110', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['104', '109'])).
% 12.90/13.10  thf('111', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['103', '110'])).
% 12.90/13.10  thf('112', plain,
% 12.90/13.10      (((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['76', '81', '111'])).
% 12.90/13.10  thf(t17_xboole_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 12.90/13.10  thf('113', plain,
% 12.90/13.10      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 12.90/13.10      inference('cnf', [status(esa)], [t17_xboole_1])).
% 12.90/13.10  thf('114', plain,
% 12.90/13.10      (![X57 : $i, X59 : $i]:
% 12.90/13.10         ((m1_subset_1 @ X57 @ (k1_zfmisc_1 @ X59)) | ~ (r1_tarski @ X57 @ X59))),
% 12.90/13.10      inference('cnf', [status(esa)], [t3_subset])).
% 12.90/13.10  thf('115', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['113', '114'])).
% 12.90/13.10  thf('116', plain,
% 12.90/13.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf(redefinition_k4_subset_1, axiom,
% 12.90/13.10    (![A:$i,B:$i,C:$i]:
% 12.90/13.10     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 12.90/13.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 12.90/13.10       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 12.90/13.10  thf('117', plain,
% 12.90/13.10      (![X44 : $i, X45 : $i, X46 : $i]:
% 12.90/13.10         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 12.90/13.10          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X45))
% 12.90/13.10          | ((k4_subset_1 @ X45 @ X44 @ X46) = (k2_xboole_0 @ X44 @ X46)))),
% 12.90/13.10      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 12.90/13.10  thf('118', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 12.90/13.10            = (k2_xboole_0 @ sk_B_1 @ X0))
% 12.90/13.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 12.90/13.10      inference('sup-', [status(thm)], ['116', '117'])).
% 12.90/13.10  thf('119', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 12.90/13.10           (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 12.90/13.10           = (k2_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['115', '118'])).
% 12.90/13.10  thf('120', plain,
% 12.90/13.10      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 12.90/13.10         (k2_tops_1 @ sk_A @ sk_B_1))
% 12.90/13.10         = (k2_xboole_0 @ sk_B_1 @ 
% 12.90/13.10            (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 12.90/13.10      inference('sup+', [status(thm)], ['112', '119'])).
% 12.90/13.10  thf('121', plain,
% 12.90/13.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf(t65_tops_1, axiom,
% 12.90/13.10    (![A:$i]:
% 12.90/13.10     ( ( l1_pre_topc @ A ) =>
% 12.90/13.10       ( ![B:$i]:
% 12.90/13.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.90/13.10           ( ( k2_pre_topc @ A @ B ) =
% 12.90/13.10             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 12.90/13.10  thf('122', plain,
% 12.90/13.10      (![X71 : $i, X72 : $i]:
% 12.90/13.10         (~ (m1_subset_1 @ X71 @ (k1_zfmisc_1 @ (u1_struct_0 @ X72)))
% 12.90/13.10          | ((k2_pre_topc @ X72 @ X71)
% 12.90/13.10              = (k4_subset_1 @ (u1_struct_0 @ X72) @ X71 @ 
% 12.90/13.10                 (k2_tops_1 @ X72 @ X71)))
% 12.90/13.10          | ~ (l1_pre_topc @ X72))),
% 12.90/13.10      inference('cnf', [status(esa)], [t65_tops_1])).
% 12.90/13.10  thf('123', plain,
% 12.90/13.10      ((~ (l1_pre_topc @ sk_A)
% 12.90/13.10        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 12.90/13.10            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 12.90/13.10               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 12.90/13.10      inference('sup-', [status(thm)], ['121', '122'])).
% 12.90/13.10  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf('125', plain,
% 12.90/13.10      (((k2_pre_topc @ sk_A @ sk_B_1)
% 12.90/13.10         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 12.90/13.10            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['123', '124'])).
% 12.90/13.10  thf('126', plain,
% 12.90/13.10      (((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['76', '81', '111'])).
% 12.90/13.10  thf('127', plain,
% 12.90/13.10      (((k2_pre_topc @ sk_A @ sk_B_1)
% 12.90/13.10         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['120', '125', '126'])).
% 12.90/13.10  thf('128', plain,
% 12.90/13.10      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 12.90/13.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.90/13.10  thf('129', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 12.90/13.10      inference('sup+', [status(thm)], ['127', '128'])).
% 12.90/13.10  thf('130', plain,
% 12.90/13.10      (((k1_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10         = (k6_subset_1 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['17', '18', '23'])).
% 12.90/13.10  thf('131', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 12.90/13.10      inference('sup-', [status(thm)], ['25', '26'])).
% 12.90/13.10  thf('132', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 12.90/13.10      inference('sup+', [status(thm)], ['130', '131'])).
% 12.90/13.10  thf('133', plain,
% 12.90/13.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 12.90/13.10         (~ (r1_tarski @ X7 @ X8)
% 12.90/13.10          | ~ (r1_tarski @ X8 @ X9)
% 12.90/13.10          | (r1_tarski @ X7 @ X9))),
% 12.90/13.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 12.90/13.10  thf('134', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0)
% 12.90/13.10          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['132', '133'])).
% 12.90/13.10  thf('135', plain,
% 12.90/13.10      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 12.90/13.10      inference('sup-', [status(thm)], ['129', '134'])).
% 12.90/13.10  thf('136', plain,
% 12.90/13.10      (![X57 : $i, X59 : $i]:
% 12.90/13.10         ((m1_subset_1 @ X57 @ (k1_zfmisc_1 @ X59)) | ~ (r1_tarski @ X57 @ X59))),
% 12.90/13.10      inference('cnf', [status(esa)], [t3_subset])).
% 12.90/13.10  thf('137', plain,
% 12.90/13.10      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 12.90/13.10        (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['135', '136'])).
% 12.90/13.10  thf(involutiveness_k3_subset_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 12.90/13.10       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 12.90/13.10  thf('138', plain,
% 12.90/13.10      (![X42 : $i, X43 : $i]:
% 12.90/13.10         (((k3_subset_1 @ X43 @ (k3_subset_1 @ X43 @ X42)) = (X42))
% 12.90/13.10          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 12.90/13.10      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 12.90/13.10  thf('139', plain,
% 12.90/13.10      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 12.90/13.10         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 12.90/13.10          (k1_tops_1 @ sk_A @ sk_B_1)))
% 12.90/13.10         = (k1_tops_1 @ sk_A @ sk_B_1))),
% 12.90/13.10      inference('sup-', [status(thm)], ['137', '138'])).
% 12.90/13.10  thf('140', plain,
% 12.90/13.10      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 12.90/13.10        (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['135', '136'])).
% 12.90/13.10  thf(d5_subset_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 12.90/13.10       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 12.90/13.10  thf('141', plain,
% 12.90/13.10      (![X29 : $i, X30 : $i]:
% 12.90/13.10         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 12.90/13.10          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 12.90/13.10      inference('cnf', [status(esa)], [d5_subset_1])).
% 12.90/13.10  thf('142', plain,
% 12.90/13.10      (![X47 : $i, X48 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 12.90/13.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.90/13.10  thf('143', plain,
% 12.90/13.10      (![X29 : $i, X30 : $i]:
% 12.90/13.10         (((k3_subset_1 @ X29 @ X30) = (k6_subset_1 @ X29 @ X30))
% 12.90/13.10          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 12.90/13.10      inference('demod', [status(thm)], ['141', '142'])).
% 12.90/13.10  thf('144', plain,
% 12.90/13.10      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 12.90/13.10         (k1_tops_1 @ sk_A @ sk_B_1))
% 12.90/13.10         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 12.90/13.10            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['140', '143'])).
% 12.90/13.10  thf('145', plain,
% 12.90/13.10      (((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['36', '37'])).
% 12.90/13.10  thf('146', plain,
% 12.90/13.10      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 12.90/13.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('demod', [status(thm)], ['47', '48'])).
% 12.90/13.10  thf('147', plain,
% 12.90/13.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf(dt_k4_subset_1, axiom,
% 12.90/13.10    (![A:$i,B:$i,C:$i]:
% 12.90/13.10     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 12.90/13.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 12.90/13.10       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 12.90/13.10  thf('148', plain,
% 12.90/13.10      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.90/13.10         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 12.90/13.10          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34))
% 12.90/13.10          | (m1_subset_1 @ (k4_subset_1 @ X34 @ X33 @ X35) @ 
% 12.90/13.10             (k1_zfmisc_1 @ X34)))),
% 12.90/13.10      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 12.90/13.10  thf('149', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 12.90/13.10           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.90/13.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 12.90/13.10      inference('sup-', [status(thm)], ['147', '148'])).
% 12.90/13.10  thf('150', plain,
% 12.90/13.10      ((m1_subset_1 @ 
% 12.90/13.10        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 12.90/13.10         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 12.90/13.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['146', '149'])).
% 12.90/13.10  thf('151', plain,
% 12.90/13.10      (((k2_pre_topc @ sk_A @ sk_B_1)
% 12.90/13.10         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 12.90/13.10            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['123', '124'])).
% 12.90/13.10  thf('152', plain,
% 12.90/13.10      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 12.90/13.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('demod', [status(thm)], ['150', '151'])).
% 12.90/13.10  thf('153', plain,
% 12.90/13.10      (![X49 : $i, X50 : $i, X51 : $i]:
% 12.90/13.10         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50))
% 12.90/13.10          | ((k7_subset_1 @ X50 @ X49 @ X51) = (k6_subset_1 @ X49 @ X51)))),
% 12.90/13.10      inference('demod', [status(thm)], ['20', '21'])).
% 12.90/13.10  thf('154', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 12.90/13.10           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['152', '153'])).
% 12.90/13.10  thf('155', plain,
% 12.90/13.10      (((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10         = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 12.90/13.10            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['145', '154'])).
% 12.90/13.10  thf('156', plain,
% 12.90/13.10      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 12.90/13.10         (k1_tops_1 @ sk_A @ sk_B_1)) = (k2_tops_1 @ sk_A @ sk_B_1))),
% 12.90/13.10      inference('demod', [status(thm)], ['144', '155'])).
% 12.90/13.10  thf('157', plain,
% 12.90/13.10      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 12.90/13.10         (k2_tops_1 @ sk_A @ sk_B_1)) = (k1_tops_1 @ sk_A @ sk_B_1))),
% 12.90/13.10      inference('demod', [status(thm)], ['139', '156'])).
% 12.90/13.10  thf('158', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 12.90/13.10           = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['152', '153'])).
% 12.90/13.10  thf('159', plain,
% 12.90/13.10      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 12.90/13.10         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 12.90/13.10      inference('split', [status(esa)], ['3'])).
% 12.90/13.10  thf('160', plain,
% 12.90/13.10      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10          = (k6_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 12.90/13.10         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 12.90/13.10      inference('sup+', [status(thm)], ['158', '159'])).
% 12.90/13.10  thf('161', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['113', '114'])).
% 12.90/13.10  thf('162', plain,
% 12.90/13.10      (![X42 : $i, X43 : $i]:
% 12.90/13.10         (((k3_subset_1 @ X43 @ (k3_subset_1 @ X43 @ X42)) = (X42))
% 12.90/13.10          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 12.90/13.10      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 12.90/13.10  thf('163', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 12.90/13.10           = (k3_xboole_0 @ X0 @ X1))),
% 12.90/13.10      inference('sup-', [status(thm)], ['161', '162'])).
% 12.90/13.10  thf('164', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['113', '114'])).
% 12.90/13.10  thf('165', plain,
% 12.90/13.10      (![X29 : $i, X30 : $i]:
% 12.90/13.10         (((k3_subset_1 @ X29 @ X30) = (k6_subset_1 @ X29 @ X30))
% 12.90/13.10          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 12.90/13.10      inference('demod', [status(thm)], ['141', '142'])).
% 12.90/13.10  thf('166', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 12.90/13.10           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['164', '165'])).
% 12.90/13.10  thf('167', plain,
% 12.90/13.10      (![X19 : $i, X20 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 12.90/13.10           = (k6_subset_1 @ X19 @ X20))),
% 12.90/13.10      inference('demod', [status(thm)], ['61', '62', '63'])).
% 12.90/13.10  thf('168', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 12.90/13.10           = (k6_subset_1 @ X0 @ X1))),
% 12.90/13.10      inference('demod', [status(thm)], ['166', '167'])).
% 12.90/13.10  thf('169', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 12.90/13.10           = (k3_xboole_0 @ X0 @ X1))),
% 12.90/13.10      inference('demod', [status(thm)], ['163', '168'])).
% 12.90/13.10  thf('170', plain,
% 12.90/13.10      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 12.90/13.10          (k2_tops_1 @ sk_A @ sk_B_1))
% 12.90/13.10          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 12.90/13.10         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 12.90/13.10      inference('sup+', [status(thm)], ['160', '169'])).
% 12.90/13.10  thf('171', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 12.90/13.10      inference('sup+', [status(thm)], ['79', '80'])).
% 12.90/13.10  thf('172', plain,
% 12.90/13.10      (((k2_pre_topc @ sk_A @ sk_B_1)
% 12.90/13.10         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['120', '125', '126'])).
% 12.90/13.10  thf('173', plain,
% 12.90/13.10      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 12.90/13.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.90/13.10  thf('174', plain,
% 12.90/13.10      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 12.90/13.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.90/13.10  thf('175', plain,
% 12.90/13.10      (![X7 : $i, X8 : $i, X9 : $i]:
% 12.90/13.10         (~ (r1_tarski @ X7 @ X8)
% 12.90/13.10          | ~ (r1_tarski @ X8 @ X9)
% 12.90/13.10          | (r1_tarski @ X7 @ X9))),
% 12.90/13.10      inference('cnf', [status(esa)], [t1_xboole_1])).
% 12.90/13.10  thf('176', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.90/13.10         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 12.90/13.10      inference('sup-', [status(thm)], ['174', '175'])).
% 12.90/13.10  thf('177', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.90/13.10         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['173', '176'])).
% 12.90/13.10  thf('178', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         (r1_tarski @ sk_B_1 @ 
% 12.90/13.10          (k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['172', '177'])).
% 12.90/13.10  thf('179', plain,
% 12.90/13.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.10         ((r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18)
% 12.90/13.10          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 12.90/13.10      inference('demod', [status(thm)], ['55', '56'])).
% 12.90/13.10  thf('180', plain,
% 12.90/13.10      (![X0 : $i]:
% 12.90/13.10         (r1_tarski @ (k6_subset_1 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 12.90/13.10          X0)),
% 12.90/13.10      inference('sup-', [status(thm)], ['178', '179'])).
% 12.90/13.10  thf('181', plain,
% 12.90/13.10      (![X21 : $i, X22 : $i]: (r1_tarski @ X21 @ (k2_xboole_0 @ X21 @ X22))),
% 12.90/13.10      inference('cnf', [status(esa)], [t7_xboole_1])).
% 12.90/13.10  thf('182', plain,
% 12.90/13.10      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.90/13.10         ((r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X18)
% 12.90/13.10          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 12.90/13.10      inference('demod', [status(thm)], ['55', '56'])).
% 12.90/13.10  thf('183', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 12.90/13.10      inference('sup-', [status(thm)], ['181', '182'])).
% 12.90/13.10  thf('184', plain,
% 12.90/13.10      (![X15 : $i]:
% 12.90/13.10         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 12.90/13.10      inference('cnf', [status(esa)], [t3_xboole_1])).
% 12.90/13.10  thf('185', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['183', '184'])).
% 12.90/13.10  thf('186', plain,
% 12.90/13.10      (![X15 : $i]:
% 12.90/13.10         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 12.90/13.10      inference('cnf', [status(esa)], [t3_xboole_1])).
% 12.90/13.10  thf('187', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         (~ (r1_tarski @ X1 @ (k6_subset_1 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 12.90/13.10      inference('sup-', [status(thm)], ['185', '186'])).
% 12.90/13.10  thf('188', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((X1)
% 12.90/13.10           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 12.90/13.10      inference('demod', [status(thm)], ['68', '73', '74'])).
% 12.90/13.10  thf('189', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['183', '184'])).
% 12.90/13.10  thf('190', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['103', '110'])).
% 12.90/13.10  thf('191', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((X1) = (k5_xboole_0 @ X1 @ (k6_subset_1 @ X0 @ X0)))),
% 12.90/13.10      inference('sup+', [status(thm)], ['189', '190'])).
% 12.90/13.10  thf('192', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['188', '191'])).
% 12.90/13.10  thf(t100_xboole_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 12.90/13.10  thf('193', plain,
% 12.90/13.10      (![X3 : $i, X4 : $i]:
% 12.90/13.10         ((k4_xboole_0 @ X3 @ X4)
% 12.90/13.10           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 12.90/13.10      inference('cnf', [status(esa)], [t100_xboole_1])).
% 12.90/13.10  thf('194', plain,
% 12.90/13.10      (![X47 : $i, X48 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X47 @ X48) = (k4_xboole_0 @ X47 @ X48))),
% 12.90/13.10      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 12.90/13.10  thf('195', plain,
% 12.90/13.10      (![X3 : $i, X4 : $i]:
% 12.90/13.10         ((k6_subset_1 @ X3 @ X4)
% 12.90/13.10           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 12.90/13.10      inference('demod', [status(thm)], ['193', '194'])).
% 12.90/13.10  thf('196', plain,
% 12.90/13.10      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['192', '195'])).
% 12.90/13.10  thf('197', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 12.90/13.10      inference('demod', [status(thm)], ['187', '196'])).
% 12.90/13.10  thf('198', plain,
% 12.90/13.10      (((k6_subset_1 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 12.90/13.10      inference('sup-', [status(thm)], ['180', '197'])).
% 12.90/13.10  thf('199', plain,
% 12.90/13.10      (![X0 : $i, X1 : $i]:
% 12.90/13.10         ((X1)
% 12.90/13.10           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k6_subset_1 @ X1 @ X0)))),
% 12.90/13.10      inference('demod', [status(thm)], ['68', '73', '74'])).
% 12.90/13.10  thf('200', plain,
% 12.90/13.10      (((sk_B_1)
% 12.90/13.10         = (k5_xboole_0 @ 
% 12.90/13.10            (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)) @ 
% 12.90/13.10            k1_xboole_0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['198', '199'])).
% 12.90/13.10  thf('201', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 12.90/13.10      inference('sup+', [status(thm)], ['103', '110'])).
% 12.90/13.10  thf('202', plain,
% 12.90/13.10      (((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 12.90/13.10      inference('demod', [status(thm)], ['200', '201'])).
% 12.90/13.10  thf('203', plain,
% 12.90/13.10      ((((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 12.90/13.10          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 12.90/13.10         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 12.90/13.10      inference('demod', [status(thm)], ['170', '171', '202'])).
% 12.90/13.10  thf('204', plain,
% 12.90/13.10      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 12.90/13.10         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 12.90/13.10      inference('sup+', [status(thm)], ['157', '203'])).
% 12.90/13.10  thf('205', plain,
% 12.90/13.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf(fc9_tops_1, axiom,
% 12.90/13.10    (![A:$i,B:$i]:
% 12.90/13.10     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 12.90/13.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 12.90/13.10       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 12.90/13.10  thf('206', plain,
% 12.90/13.10      (![X62 : $i, X63 : $i]:
% 12.90/13.10         (~ (l1_pre_topc @ X62)
% 12.90/13.10          | ~ (v2_pre_topc @ X62)
% 12.90/13.10          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 12.90/13.10          | (v3_pre_topc @ (k1_tops_1 @ X62 @ X63) @ X62))),
% 12.90/13.10      inference('cnf', [status(esa)], [fc9_tops_1])).
% 12.90/13.10  thf('207', plain,
% 12.90/13.10      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 12.90/13.10        | ~ (v2_pre_topc @ sk_A)
% 12.90/13.10        | ~ (l1_pre_topc @ sk_A))),
% 12.90/13.10      inference('sup-', [status(thm)], ['205', '206'])).
% 12.90/13.10  thf('208', plain, ((v2_pre_topc @ sk_A)),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf('209', plain, ((l1_pre_topc @ sk_A)),
% 12.90/13.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.90/13.10  thf('210', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 12.90/13.10      inference('demod', [status(thm)], ['207', '208', '209'])).
% 12.90/13.10  thf('211', plain,
% 12.90/13.10      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 12.90/13.10         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 12.90/13.10      inference('sup+', [status(thm)], ['204', '210'])).
% 12.90/13.10  thf('212', plain,
% 12.90/13.10      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 12.90/13.10      inference('split', [status(esa)], ['0'])).
% 12.90/13.10  thf('213', plain,
% 12.90/13.10      (~
% 12.90/13.10       (((k2_tops_1 @ sk_A @ sk_B_1)
% 12.90/13.10          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 12.90/13.10             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 12.90/13.10       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 12.90/13.10      inference('sup-', [status(thm)], ['211', '212'])).
% 12.90/13.10  thf('214', plain, ($false),
% 12.90/13.10      inference('sat_resolution*', [status(thm)], ['1', '42', '43', '213'])).
% 12.90/13.10  
% 12.90/13.10  % SZS output end Refutation
% 12.90/13.10  
% 12.90/13.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
