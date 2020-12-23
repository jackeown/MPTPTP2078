%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mo4d202GOn

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:26 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 469 expanded)
%              Number of leaves         :   36 ( 143 expanded)
%              Depth                    :   18
%              Number of atoms          : 1197 (5137 expanded)
%              Number of equality atoms :   58 ( 147 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t88_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_tops_1])).

thf('0',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tops_1 @ X42 @ X43 )
      | ( ( k1_tops_1 @ X43 @ X42 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k2_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ X33 ) @ ( k1_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','18'])).

thf('20',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['7','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( ( k2_pre_topc @ X41 @ X40 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X41 ) @ X40 @ ( k2_tops_1 @ X41 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k4_subset_1 @ X18 @ X17 @ X19 )
        = ( k2_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('52',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','18'])).

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('59',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('62',plain,
    ( ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('64',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X36 @ X35 ) @ X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('68',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('72',plain,
    ( ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('74',plain,
    ( ( ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_xboole_0
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k1_tops_1 @ X43 @ X42 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X42 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('84',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['35','84'])).

thf('86',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['35','84','86'])).

thf('88',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['34','85','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('91',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X27 @ ( k4_subset_1 @ X27 @ X28 @ X26 ) ) @ ( k3_subset_1 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('95',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39','48'])).

thf('96',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['93','96'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('98',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X24 @ X23 ) @ ( k3_subset_1 @ X24 @ X25 ) )
      | ( r1_tarski @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('99',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('102',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['88','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mo4d202GOn
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.50/1.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.50/1.77  % Solved by: fo/fo7.sh
% 1.50/1.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.77  % done 782 iterations in 1.312s
% 1.50/1.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.50/1.77  % SZS output start Refutation
% 1.50/1.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.50/1.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.50/1.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.50/1.77  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.77  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.50/1.77  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.50/1.77  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.50/1.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.50/1.77  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.77  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.50/1.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.50/1.77  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.50/1.77  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.50/1.77  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.50/1.77  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.50/1.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.77  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.50/1.77  thf(t88_tops_1, conjecture,
% 1.50/1.77    (![A:$i]:
% 1.50/1.77     ( ( l1_pre_topc @ A ) =>
% 1.50/1.77       ( ![B:$i]:
% 1.50/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.77           ( ( v2_tops_1 @ B @ A ) <=>
% 1.50/1.77             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.50/1.77  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.77    (~( ![A:$i]:
% 1.50/1.77        ( ( l1_pre_topc @ A ) =>
% 1.50/1.77          ( ![B:$i]:
% 1.50/1.77            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.77              ( ( v2_tops_1 @ B @ A ) <=>
% 1.50/1.77                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 1.50/1.77    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 1.50/1.77  thf('0', plain,
% 1.50/1.77      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.50/1.77        | (v2_tops_1 @ sk_B @ sk_A))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('1', plain,
% 1.50/1.77      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.50/1.77      inference('split', [status(esa)], ['0'])).
% 1.50/1.77  thf('2', plain,
% 1.50/1.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf(t84_tops_1, axiom,
% 1.50/1.77    (![A:$i]:
% 1.50/1.77     ( ( l1_pre_topc @ A ) =>
% 1.50/1.77       ( ![B:$i]:
% 1.50/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.77           ( ( v2_tops_1 @ B @ A ) <=>
% 1.50/1.77             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.50/1.77  thf('3', plain,
% 1.50/1.77      (![X42 : $i, X43 : $i]:
% 1.50/1.77         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.50/1.77          | ~ (v2_tops_1 @ X42 @ X43)
% 1.50/1.77          | ((k1_tops_1 @ X43 @ X42) = (k1_xboole_0))
% 1.50/1.77          | ~ (l1_pre_topc @ X43))),
% 1.50/1.77      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.50/1.77  thf('4', plain,
% 1.50/1.77      ((~ (l1_pre_topc @ sk_A)
% 1.50/1.77        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.50/1.77        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.50/1.77      inference('sup-', [status(thm)], ['2', '3'])).
% 1.50/1.77  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('6', plain,
% 1.50/1.77      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 1.50/1.77        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.50/1.77      inference('demod', [status(thm)], ['4', '5'])).
% 1.50/1.77  thf('7', plain,
% 1.50/1.77      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.50/1.77         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.50/1.77      inference('sup-', [status(thm)], ['1', '6'])).
% 1.50/1.77  thf('8', plain,
% 1.50/1.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf(l78_tops_1, axiom,
% 1.50/1.77    (![A:$i]:
% 1.50/1.77     ( ( l1_pre_topc @ A ) =>
% 1.50/1.77       ( ![B:$i]:
% 1.50/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.77           ( ( k2_tops_1 @ A @ B ) =
% 1.50/1.77             ( k7_subset_1 @
% 1.50/1.77               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.50/1.77               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.50/1.77  thf('9', plain,
% 1.50/1.77      (![X33 : $i, X34 : $i]:
% 1.50/1.77         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.50/1.77          | ((k2_tops_1 @ X34 @ X33)
% 1.50/1.77              = (k7_subset_1 @ (u1_struct_0 @ X34) @ 
% 1.50/1.77                 (k2_pre_topc @ X34 @ X33) @ (k1_tops_1 @ X34 @ X33)))
% 1.50/1.77          | ~ (l1_pre_topc @ X34))),
% 1.50/1.77      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.50/1.77  thf('10', plain,
% 1.50/1.77      ((~ (l1_pre_topc @ sk_A)
% 1.50/1.77        | ((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.77            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.77               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('sup-', [status(thm)], ['8', '9'])).
% 1.50/1.77  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('12', plain,
% 1.50/1.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf(dt_k2_pre_topc, axiom,
% 1.50/1.77    (![A:$i,B:$i]:
% 1.50/1.77     ( ( ( l1_pre_topc @ A ) & 
% 1.50/1.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.50/1.77       ( m1_subset_1 @
% 1.50/1.77         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.50/1.77  thf('13', plain,
% 1.50/1.77      (![X29 : $i, X30 : $i]:
% 1.50/1.77         (~ (l1_pre_topc @ X29)
% 1.50/1.77          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.50/1.77          | (m1_subset_1 @ (k2_pre_topc @ X29 @ X30) @ 
% 1.50/1.77             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 1.50/1.77      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.50/1.77  thf('14', plain,
% 1.50/1.77      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.77        | ~ (l1_pre_topc @ sk_A))),
% 1.50/1.77      inference('sup-', [status(thm)], ['12', '13'])).
% 1.50/1.77  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('16', plain,
% 1.50/1.77      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('demod', [status(thm)], ['14', '15'])).
% 1.50/1.77  thf(redefinition_k7_subset_1, axiom,
% 1.50/1.77    (![A:$i,B:$i,C:$i]:
% 1.50/1.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.50/1.77       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.50/1.77  thf('17', plain,
% 1.50/1.77      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.50/1.77         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 1.50/1.77          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 1.50/1.77      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.50/1.77  thf('18', plain,
% 1.50/1.77      (![X0 : $i]:
% 1.50/1.77         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.50/1.77      inference('sup-', [status(thm)], ['16', '17'])).
% 1.50/1.77  thf('19', plain,
% 1.50/1.77      (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.77         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.77      inference('demod', [status(thm)], ['10', '11', '18'])).
% 1.50/1.77  thf('20', plain,
% 1.50/1.77      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.77          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ k1_xboole_0)))
% 1.50/1.77         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.50/1.77      inference('sup+', [status(thm)], ['7', '19'])).
% 1.50/1.77  thf(d10_xboole_0, axiom,
% 1.50/1.77    (![A:$i,B:$i]:
% 1.50/1.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.50/1.77  thf('21', plain,
% 1.50/1.77      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.50/1.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.77  thf('22', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.50/1.77      inference('simplify', [status(thm)], ['21'])).
% 1.50/1.77  thf(l32_xboole_1, axiom,
% 1.50/1.77    (![A:$i,B:$i]:
% 1.50/1.77     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.50/1.77  thf('23', plain,
% 1.50/1.77      (![X5 : $i, X7 : $i]:
% 1.50/1.77         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.50/1.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.50/1.77  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.50/1.77      inference('sup-', [status(thm)], ['22', '23'])).
% 1.50/1.77  thf(t48_xboole_1, axiom,
% 1.50/1.77    (![A:$i,B:$i]:
% 1.50/1.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.50/1.77  thf('25', plain,
% 1.50/1.77      (![X15 : $i, X16 : $i]:
% 1.50/1.77         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.50/1.77           = (k3_xboole_0 @ X15 @ X16))),
% 1.50/1.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.50/1.77  thf('26', plain,
% 1.50/1.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.50/1.77      inference('sup+', [status(thm)], ['24', '25'])).
% 1.50/1.77  thf('27', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.50/1.77      inference('simplify', [status(thm)], ['21'])).
% 1.50/1.77  thf(t28_xboole_1, axiom,
% 1.50/1.77    (![A:$i,B:$i]:
% 1.50/1.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.50/1.77  thf('28', plain,
% 1.50/1.77      (![X13 : $i, X14 : $i]:
% 1.50/1.77         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.50/1.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.50/1.77  thf('29', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.50/1.77      inference('sup-', [status(thm)], ['27', '28'])).
% 1.50/1.77  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.50/1.77      inference('demod', [status(thm)], ['26', '29'])).
% 1.50/1.77  thf('31', plain,
% 1.50/1.77      ((((k2_tops_1 @ sk_A @ sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 1.50/1.77         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.50/1.77      inference('demod', [status(thm)], ['20', '30'])).
% 1.50/1.77  thf('32', plain,
% 1.50/1.77      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.50/1.77        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('33', plain,
% 1.50/1.77      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.50/1.77         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('split', [status(esa)], ['32'])).
% 1.50/1.77  thf('34', plain,
% 1.50/1.77      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))
% 1.50/1.77         <= (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) & 
% 1.50/1.77             ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.50/1.77      inference('sup-', [status(thm)], ['31', '33'])).
% 1.50/1.77  thf('35', plain,
% 1.50/1.77      (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) | 
% 1.50/1.77       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.50/1.77      inference('split', [status(esa)], ['32'])).
% 1.50/1.77  thf('36', plain,
% 1.50/1.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf(t65_tops_1, axiom,
% 1.50/1.77    (![A:$i]:
% 1.50/1.77     ( ( l1_pre_topc @ A ) =>
% 1.50/1.77       ( ![B:$i]:
% 1.50/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.77           ( ( k2_pre_topc @ A @ B ) =
% 1.50/1.77             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.50/1.77  thf('37', plain,
% 1.50/1.77      (![X40 : $i, X41 : $i]:
% 1.50/1.77         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 1.50/1.77          | ((k2_pre_topc @ X41 @ X40)
% 1.50/1.77              = (k4_subset_1 @ (u1_struct_0 @ X41) @ X40 @ 
% 1.50/1.77                 (k2_tops_1 @ X41 @ X40)))
% 1.50/1.77          | ~ (l1_pre_topc @ X41))),
% 1.50/1.77      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.50/1.77  thf('38', plain,
% 1.50/1.77      ((~ (l1_pre_topc @ sk_A)
% 1.50/1.77        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.50/1.77            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.50/1.77               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('sup-', [status(thm)], ['36', '37'])).
% 1.50/1.77  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('40', plain,
% 1.50/1.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf(dt_k2_tops_1, axiom,
% 1.50/1.77    (![A:$i,B:$i]:
% 1.50/1.77     ( ( ( l1_pre_topc @ A ) & 
% 1.50/1.77         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.50/1.77       ( m1_subset_1 @
% 1.50/1.77         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.50/1.77  thf('41', plain,
% 1.50/1.77      (![X31 : $i, X32 : $i]:
% 1.50/1.77         (~ (l1_pre_topc @ X31)
% 1.50/1.77          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.50/1.77          | (m1_subset_1 @ (k2_tops_1 @ X31 @ X32) @ 
% 1.50/1.77             (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 1.50/1.77      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.50/1.77  thf('42', plain,
% 1.50/1.77      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.50/1.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.77        | ~ (l1_pre_topc @ sk_A))),
% 1.50/1.77      inference('sup-', [status(thm)], ['40', '41'])).
% 1.50/1.77  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('44', plain,
% 1.50/1.77      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.50/1.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('demod', [status(thm)], ['42', '43'])).
% 1.50/1.77  thf('45', plain,
% 1.50/1.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf(redefinition_k4_subset_1, axiom,
% 1.50/1.77    (![A:$i,B:$i,C:$i]:
% 1.50/1.77     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.50/1.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.50/1.77       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.50/1.77  thf('46', plain,
% 1.50/1.77      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.50/1.77         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 1.50/1.77          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18))
% 1.50/1.77          | ((k4_subset_1 @ X18 @ X17 @ X19) = (k2_xboole_0 @ X17 @ X19)))),
% 1.50/1.77      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.50/1.77  thf('47', plain,
% 1.50/1.77      (![X0 : $i]:
% 1.50/1.77         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.50/1.77            = (k2_xboole_0 @ sk_B @ X0))
% 1.50/1.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.50/1.77      inference('sup-', [status(thm)], ['45', '46'])).
% 1.50/1.77  thf('48', plain,
% 1.50/1.77      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.50/1.77         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.77      inference('sup-', [status(thm)], ['44', '47'])).
% 1.50/1.77  thf('49', plain,
% 1.50/1.77      (((k2_pre_topc @ sk_A @ sk_B)
% 1.50/1.77         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.77      inference('demod', [status(thm)], ['38', '39', '48'])).
% 1.50/1.77  thf('50', plain,
% 1.50/1.77      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('split', [status(esa)], ['0'])).
% 1.50/1.77  thf(t12_xboole_1, axiom,
% 1.50/1.77    (![A:$i,B:$i]:
% 1.50/1.77     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.50/1.77  thf('51', plain,
% 1.50/1.77      (![X8 : $i, X9 : $i]:
% 1.50/1.77         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 1.50/1.77      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.50/1.77  thf('52', plain,
% 1.50/1.77      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.50/1.77          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('sup-', [status(thm)], ['50', '51'])).
% 1.50/1.77  thf('53', plain,
% 1.50/1.77      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('sup+', [status(thm)], ['49', '52'])).
% 1.50/1.77  thf('54', plain,
% 1.50/1.77      (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.77         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.77      inference('demod', [status(thm)], ['10', '11', '18'])).
% 1.50/1.77  thf('55', plain,
% 1.50/1.77      (![X15 : $i, X16 : $i]:
% 1.50/1.77         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.50/1.77           = (k3_xboole_0 @ X15 @ X16))),
% 1.50/1.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.50/1.77  thf('56', plain,
% 1.50/1.77      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.50/1.77         = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.77      inference('sup+', [status(thm)], ['54', '55'])).
% 1.50/1.77  thf('57', plain,
% 1.50/1.77      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77          (k2_pre_topc @ sk_A @ sk_B))
% 1.50/1.77          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77             (k1_tops_1 @ sk_A @ sk_B))))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('sup+', [status(thm)], ['53', '56'])).
% 1.50/1.77  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.50/1.77      inference('sup-', [status(thm)], ['22', '23'])).
% 1.50/1.77  thf('59', plain,
% 1.50/1.77      ((((k1_xboole_0)
% 1.50/1.77          = (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77             (k1_tops_1 @ sk_A @ sk_B))))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('demod', [status(thm)], ['57', '58'])).
% 1.50/1.77  thf('60', plain,
% 1.50/1.77      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('split', [status(esa)], ['0'])).
% 1.50/1.77  thf('61', plain,
% 1.50/1.77      ((((k2_pre_topc @ sk_A @ sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('sup+', [status(thm)], ['49', '52'])).
% 1.50/1.77  thf('62', plain,
% 1.50/1.77      (((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('demod', [status(thm)], ['60', '61'])).
% 1.50/1.77  thf('63', plain,
% 1.50/1.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf(t44_tops_1, axiom,
% 1.50/1.77    (![A:$i]:
% 1.50/1.77     ( ( l1_pre_topc @ A ) =>
% 1.50/1.77       ( ![B:$i]:
% 1.50/1.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.77           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.50/1.77  thf('64', plain,
% 1.50/1.77      (![X35 : $i, X36 : $i]:
% 1.50/1.77         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.50/1.77          | (r1_tarski @ (k1_tops_1 @ X36 @ X35) @ X35)
% 1.50/1.77          | ~ (l1_pre_topc @ X36))),
% 1.50/1.77      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.50/1.77  thf('65', plain,
% 1.50/1.77      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.50/1.77      inference('sup-', [status(thm)], ['63', '64'])).
% 1.50/1.77  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('67', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.50/1.77      inference('demod', [status(thm)], ['65', '66'])).
% 1.50/1.77  thf(t1_xboole_1, axiom,
% 1.50/1.77    (![A:$i,B:$i,C:$i]:
% 1.50/1.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.50/1.77       ( r1_tarski @ A @ C ) ))).
% 1.50/1.77  thf('68', plain,
% 1.50/1.77      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.50/1.77         (~ (r1_tarski @ X10 @ X11)
% 1.50/1.77          | ~ (r1_tarski @ X11 @ X12)
% 1.50/1.77          | (r1_tarski @ X10 @ X12))),
% 1.50/1.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.50/1.77  thf('69', plain,
% 1.50/1.77      (![X0 : $i]:
% 1.50/1.77         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.50/1.77          | ~ (r1_tarski @ sk_B @ X0))),
% 1.50/1.77      inference('sup-', [status(thm)], ['67', '68'])).
% 1.50/1.77  thf('70', plain,
% 1.50/1.77      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('sup-', [status(thm)], ['62', '69'])).
% 1.50/1.77  thf('71', plain,
% 1.50/1.77      (![X13 : $i, X14 : $i]:
% 1.50/1.77         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.50/1.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.50/1.77  thf('72', plain,
% 1.50/1.77      ((((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_B))
% 1.50/1.77          = (k1_tops_1 @ sk_A @ sk_B)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('sup-', [status(thm)], ['70', '71'])).
% 1.50/1.77  thf(commutativity_k3_xboole_0, axiom,
% 1.50/1.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.50/1.77  thf('73', plain,
% 1.50/1.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.50/1.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.50/1.77  thf('74', plain,
% 1.50/1.77      ((((k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.50/1.77          = (k1_tops_1 @ sk_A @ sk_B)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('demod', [status(thm)], ['72', '73'])).
% 1.50/1.77  thf('75', plain,
% 1.50/1.77      ((((k1_xboole_0) = (k1_tops_1 @ sk_A @ sk_B)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('sup+', [status(thm)], ['59', '74'])).
% 1.50/1.77  thf('76', plain,
% 1.50/1.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('77', plain,
% 1.50/1.77      (![X42 : $i, X43 : $i]:
% 1.50/1.77         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 1.50/1.77          | ((k1_tops_1 @ X43 @ X42) != (k1_xboole_0))
% 1.50/1.77          | (v2_tops_1 @ X42 @ X43)
% 1.50/1.77          | ~ (l1_pre_topc @ X43))),
% 1.50/1.77      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.50/1.77  thf('78', plain,
% 1.50/1.77      ((~ (l1_pre_topc @ sk_A)
% 1.50/1.77        | (v2_tops_1 @ sk_B @ sk_A)
% 1.50/1.77        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.50/1.77      inference('sup-', [status(thm)], ['76', '77'])).
% 1.50/1.77  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('80', plain,
% 1.50/1.77      (((v2_tops_1 @ sk_B @ sk_A)
% 1.50/1.77        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 1.50/1.77      inference('demod', [status(thm)], ['78', '79'])).
% 1.50/1.77  thf('81', plain,
% 1.50/1.77      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('sup-', [status(thm)], ['75', '80'])).
% 1.50/1.77  thf('82', plain,
% 1.50/1.77      (((v2_tops_1 @ sk_B @ sk_A))
% 1.50/1.77         <= (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.77      inference('simplify', [status(thm)], ['81'])).
% 1.50/1.77  thf('83', plain,
% 1.50/1.77      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.50/1.77      inference('split', [status(esa)], ['32'])).
% 1.50/1.77  thf('84', plain,
% 1.50/1.77      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 1.50/1.77       ~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.77      inference('sup-', [status(thm)], ['82', '83'])).
% 1.50/1.77  thf('85', plain, (~ ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.77      inference('sat_resolution*', [status(thm)], ['35', '84'])).
% 1.50/1.77  thf('86', plain,
% 1.50/1.77      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 1.50/1.77       ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.77      inference('split', [status(esa)], ['0'])).
% 1.50/1.77  thf('87', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 1.50/1.77      inference('sat_resolution*', [status(thm)], ['35', '84', '86'])).
% 1.50/1.77  thf('88', plain, (~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 1.50/1.77      inference('simpl_trail', [status(thm)], ['34', '85', '87'])).
% 1.50/1.77  thf('89', plain,
% 1.50/1.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('90', plain,
% 1.50/1.77      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.50/1.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('demod', [status(thm)], ['42', '43'])).
% 1.50/1.77  thf(t41_subset_1, axiom,
% 1.50/1.77    (![A:$i,B:$i]:
% 1.50/1.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.50/1.77       ( ![C:$i]:
% 1.50/1.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.50/1.77           ( r1_tarski @
% 1.50/1.77             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.50/1.77             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 1.50/1.77  thf('91', plain,
% 1.50/1.77      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.50/1.77         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 1.50/1.77          | (r1_tarski @ 
% 1.50/1.77             (k3_subset_1 @ X27 @ (k4_subset_1 @ X27 @ X28 @ X26)) @ 
% 1.50/1.77             (k3_subset_1 @ X27 @ X28))
% 1.50/1.77          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.50/1.77      inference('cnf', [status(esa)], [t41_subset_1])).
% 1.50/1.77  thf('92', plain,
% 1.50/1.77      (![X0 : $i]:
% 1.50/1.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.77          | (r1_tarski @ 
% 1.50/1.77             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.77              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.50/1.77               (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.50/1.77             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.50/1.77      inference('sup-', [status(thm)], ['90', '91'])).
% 1.50/1.77  thf('93', plain,
% 1.50/1.77      ((r1_tarski @ 
% 1.50/1.77        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.77         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.50/1.77        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.50/1.77      inference('sup-', [status(thm)], ['89', '92'])).
% 1.50/1.77  thf('94', plain,
% 1.50/1.77      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.50/1.77         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.77      inference('sup-', [status(thm)], ['44', '47'])).
% 1.50/1.77  thf('95', plain,
% 1.50/1.77      (((k2_pre_topc @ sk_A @ sk_B)
% 1.50/1.77         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.77      inference('demod', [status(thm)], ['38', '39', '48'])).
% 1.50/1.77  thf('96', plain,
% 1.50/1.77      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.50/1.77         = (k2_pre_topc @ sk_A @ sk_B))),
% 1.50/1.77      inference('demod', [status(thm)], ['94', '95'])).
% 1.50/1.77  thf('97', plain,
% 1.50/1.77      ((r1_tarski @ 
% 1.50/1.77        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.50/1.77        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.50/1.77      inference('demod', [status(thm)], ['93', '96'])).
% 1.50/1.77  thf(t31_subset_1, axiom,
% 1.50/1.77    (![A:$i,B:$i]:
% 1.50/1.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.50/1.77       ( ![C:$i]:
% 1.50/1.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.50/1.77           ( ( r1_tarski @ B @ C ) <=>
% 1.50/1.77             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.50/1.77  thf('98', plain,
% 1.50/1.77      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.50/1.77         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 1.50/1.77          | ~ (r1_tarski @ (k3_subset_1 @ X24 @ X23) @ 
% 1.50/1.77               (k3_subset_1 @ X24 @ X25))
% 1.50/1.77          | (r1_tarski @ X25 @ X23)
% 1.50/1.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 1.50/1.77      inference('cnf', [status(esa)], [t31_subset_1])).
% 1.50/1.77  thf('99', plain,
% 1.50/1.77      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.77        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 1.50/1.77        | ~ (m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.50/1.77      inference('sup-', [status(thm)], ['97', '98'])).
% 1.50/1.77  thf('100', plain,
% 1.50/1.77      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.77  thf('101', plain,
% 1.50/1.77      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.77      inference('demod', [status(thm)], ['14', '15'])).
% 1.50/1.77  thf('102', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 1.50/1.77      inference('demod', [status(thm)], ['99', '100', '101'])).
% 1.50/1.77  thf('103', plain, ($false), inference('demod', [status(thm)], ['88', '102'])).
% 1.50/1.77  
% 1.50/1.77  % SZS output end Refutation
% 1.50/1.77  
% 1.50/1.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
