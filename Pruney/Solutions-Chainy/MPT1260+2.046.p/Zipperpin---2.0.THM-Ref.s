%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6li0hPyEPp

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:29 EST 2020

% Result     : Theorem 9.28s
% Output     : Refutation 9.28s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 367 expanded)
%              Number of leaves         :   39 ( 117 expanded)
%              Depth                    :   16
%              Number of atoms          : 1499 (4758 expanded)
%              Number of equality atoms :   84 ( 234 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v3_pre_topc @ X47 @ X48 )
      | ~ ( r1_tarski @ X47 @ X49 )
      | ( r1_tarski @ X47 @ ( k1_tops_1 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
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

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('16',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X46 @ X45 ) @ X45 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
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
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
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
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( ( k2_tops_1 @ X44 @ X43 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X44 ) @ ( k2_pre_topc @ X44 @ X43 ) @ ( k1_tops_1 @ X44 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
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

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('43',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('44',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X17 @ X16 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('53',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_pre_topc @ X51 @ X50 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 @ ( k2_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k3_subset_1 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['57','65'])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('68',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('71',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('76',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('78',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ( ( k7_subset_1 @ X32 @ X33 @ X31 )
        = ( k9_subset_1 @ X32 @ X33 @ ( k3_subset_1 @ X32 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('81',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_subset_1 @ X24 @ ( k3_subset_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
        = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k9_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('86',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 @ X2 )
      = ( k4_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('89',plain,(
    ! [X36: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( r1_tarski @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('91',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k9_subset_1 @ X21 @ X20 @ X20 )
        = X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['84','87','92'])).

thf('94',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['73','93'])).

thf('95',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['72','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('97',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ( ( k1_tops_1 @ X53 @ X52 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X53 ) @ X52 @ ( k2_tops_1 @ X53 @ X52 ) ) )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( ( k7_subset_1 @ X29 @ X28 @ X30 )
        = ( k4_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['98','99','102'])).

thf('104',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['95','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('106',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X41 @ X42 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('107',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['104','110'])).

thf('112',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6li0hPyEPp
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:14:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 9.28/9.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.28/9.46  % Solved by: fo/fo7.sh
% 9.28/9.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.28/9.46  % done 12483 iterations in 8.995s
% 9.28/9.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.28/9.46  % SZS output start Refutation
% 9.28/9.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.28/9.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.28/9.46  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 9.28/9.46  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 9.28/9.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 9.28/9.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.28/9.46  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 9.28/9.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 9.28/9.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.28/9.46  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 9.28/9.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.28/9.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.28/9.46  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 9.28/9.46  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 9.28/9.46  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 9.28/9.46  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 9.28/9.46  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 9.28/9.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 9.28/9.46  thf(sk_A_type, type, sk_A: $i).
% 9.28/9.46  thf(t76_tops_1, conjecture,
% 9.28/9.46    (![A:$i]:
% 9.28/9.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.28/9.46       ( ![B:$i]:
% 9.28/9.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.28/9.46           ( ( v3_pre_topc @ B @ A ) <=>
% 9.28/9.46             ( ( k2_tops_1 @ A @ B ) =
% 9.28/9.46               ( k7_subset_1 @
% 9.28/9.46                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 9.28/9.46  thf(zf_stmt_0, negated_conjecture,
% 9.28/9.46    (~( ![A:$i]:
% 9.28/9.46        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.28/9.46          ( ![B:$i]:
% 9.28/9.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.28/9.46              ( ( v3_pre_topc @ B @ A ) <=>
% 9.28/9.46                ( ( k2_tops_1 @ A @ B ) =
% 9.28/9.46                  ( k7_subset_1 @
% 9.28/9.46                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 9.28/9.46    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 9.28/9.46  thf('0', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 9.28/9.46        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('1', plain,
% 9.28/9.46      (~
% 9.28/9.46       (((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 9.28/9.46       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 9.28/9.46      inference('split', [status(esa)], ['0'])).
% 9.28/9.46  thf('2', plain,
% 9.28/9.46      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('3', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 9.28/9.46        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('4', plain,
% 9.28/9.46      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 9.28/9.46      inference('split', [status(esa)], ['3'])).
% 9.28/9.46  thf('5', plain,
% 9.28/9.46      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf(t56_tops_1, axiom,
% 9.28/9.46    (![A:$i]:
% 9.28/9.46     ( ( l1_pre_topc @ A ) =>
% 9.28/9.46       ( ![B:$i]:
% 9.28/9.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.28/9.46           ( ![C:$i]:
% 9.28/9.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.28/9.46               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 9.28/9.46                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 9.28/9.46  thf('6', plain,
% 9.28/9.46      (![X47 : $i, X48 : $i, X49 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 9.28/9.46          | ~ (v3_pre_topc @ X47 @ X48)
% 9.28/9.46          | ~ (r1_tarski @ X47 @ X49)
% 9.28/9.46          | (r1_tarski @ X47 @ (k1_tops_1 @ X48 @ X49))
% 9.28/9.46          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 9.28/9.46          | ~ (l1_pre_topc @ X48))),
% 9.28/9.46      inference('cnf', [status(esa)], [t56_tops_1])).
% 9.28/9.46  thf('7', plain,
% 9.28/9.46      (![X0 : $i]:
% 9.28/9.46         (~ (l1_pre_topc @ sk_A)
% 9.28/9.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.28/9.46          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 9.28/9.46          | ~ (r1_tarski @ sk_B_1 @ X0)
% 9.28/9.46          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 9.28/9.46      inference('sup-', [status(thm)], ['5', '6'])).
% 9.28/9.46  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('9', plain,
% 9.28/9.46      (![X0 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.28/9.46          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 9.28/9.46          | ~ (r1_tarski @ sk_B_1 @ X0)
% 9.28/9.46          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 9.28/9.46      inference('demod', [status(thm)], ['7', '8'])).
% 9.28/9.46  thf('10', plain,
% 9.28/9.46      ((![X0 : $i]:
% 9.28/9.46          (~ (r1_tarski @ sk_B_1 @ X0)
% 9.28/9.46           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 9.28/9.46           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 9.28/9.46         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['4', '9'])).
% 9.28/9.46  thf('11', plain,
% 9.28/9.46      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 9.28/9.46         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 9.28/9.46         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['2', '10'])).
% 9.28/9.46  thf(d10_xboole_0, axiom,
% 9.28/9.46    (![A:$i,B:$i]:
% 9.28/9.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.28/9.46  thf('12', plain,
% 9.28/9.46      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 9.28/9.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.28/9.46  thf('13', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 9.28/9.46      inference('simplify', [status(thm)], ['12'])).
% 9.28/9.46  thf('14', plain,
% 9.28/9.46      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 9.28/9.46         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 9.28/9.46      inference('demod', [status(thm)], ['11', '13'])).
% 9.28/9.46  thf('15', plain,
% 9.28/9.46      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf(t44_tops_1, axiom,
% 9.28/9.46    (![A:$i]:
% 9.28/9.46     ( ( l1_pre_topc @ A ) =>
% 9.28/9.46       ( ![B:$i]:
% 9.28/9.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.28/9.46           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 9.28/9.46  thf('16', plain,
% 9.28/9.46      (![X45 : $i, X46 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 9.28/9.46          | (r1_tarski @ (k1_tops_1 @ X46 @ X45) @ X45)
% 9.28/9.46          | ~ (l1_pre_topc @ X46))),
% 9.28/9.46      inference('cnf', [status(esa)], [t44_tops_1])).
% 9.28/9.46  thf('17', plain,
% 9.28/9.46      ((~ (l1_pre_topc @ sk_A)
% 9.28/9.46        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 9.28/9.46      inference('sup-', [status(thm)], ['15', '16'])).
% 9.28/9.46  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('19', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 9.28/9.46      inference('demod', [status(thm)], ['17', '18'])).
% 9.28/9.46  thf('20', plain,
% 9.28/9.46      (![X2 : $i, X4 : $i]:
% 9.28/9.46         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 9.28/9.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.28/9.46  thf('21', plain,
% 9.28/9.46      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 9.28/9.46        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['19', '20'])).
% 9.28/9.46  thf('22', plain,
% 9.28/9.46      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 9.28/9.46         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['14', '21'])).
% 9.28/9.46  thf('23', plain,
% 9.28/9.46      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf(l78_tops_1, axiom,
% 9.28/9.46    (![A:$i]:
% 9.28/9.46     ( ( l1_pre_topc @ A ) =>
% 9.28/9.46       ( ![B:$i]:
% 9.28/9.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.28/9.46           ( ( k2_tops_1 @ A @ B ) =
% 9.28/9.46             ( k7_subset_1 @
% 9.28/9.46               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 9.28/9.46               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 9.28/9.46  thf('24', plain,
% 9.28/9.46      (![X43 : $i, X44 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 9.28/9.46          | ((k2_tops_1 @ X44 @ X43)
% 9.28/9.46              = (k7_subset_1 @ (u1_struct_0 @ X44) @ 
% 9.28/9.46                 (k2_pre_topc @ X44 @ X43) @ (k1_tops_1 @ X44 @ X43)))
% 9.28/9.46          | ~ (l1_pre_topc @ X44))),
% 9.28/9.46      inference('cnf', [status(esa)], [l78_tops_1])).
% 9.28/9.46  thf('25', plain,
% 9.28/9.46      ((~ (l1_pre_topc @ sk_A)
% 9.28/9.46        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 9.28/9.46      inference('sup-', [status(thm)], ['23', '24'])).
% 9.28/9.46  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('27', plain,
% 9.28/9.46      (((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 9.28/9.46      inference('demod', [status(thm)], ['25', '26'])).
% 9.28/9.46  thf('28', plain,
% 9.28/9.46      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf(dt_k2_pre_topc, axiom,
% 9.28/9.46    (![A:$i,B:$i]:
% 9.28/9.46     ( ( ( l1_pre_topc @ A ) & 
% 9.28/9.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 9.28/9.46       ( m1_subset_1 @
% 9.28/9.46         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 9.28/9.46  thf('29', plain,
% 9.28/9.46      (![X39 : $i, X40 : $i]:
% 9.28/9.46         (~ (l1_pre_topc @ X39)
% 9.28/9.46          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 9.28/9.46          | (m1_subset_1 @ (k2_pre_topc @ X39 @ X40) @ 
% 9.28/9.46             (k1_zfmisc_1 @ (u1_struct_0 @ X39))))),
% 9.28/9.46      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 9.28/9.46  thf('30', plain,
% 9.28/9.46      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 9.28/9.46         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.28/9.46        | ~ (l1_pre_topc @ sk_A))),
% 9.28/9.46      inference('sup-', [status(thm)], ['28', '29'])).
% 9.28/9.46  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('32', plain,
% 9.28/9.46      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 9.28/9.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('demod', [status(thm)], ['30', '31'])).
% 9.28/9.46  thf(redefinition_k7_subset_1, axiom,
% 9.28/9.46    (![A:$i,B:$i,C:$i]:
% 9.28/9.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.28/9.46       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 9.28/9.46  thf('33', plain,
% 9.28/9.46      (![X28 : $i, X29 : $i, X30 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 9.28/9.46          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 9.28/9.46      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 9.28/9.46  thf('34', plain,
% 9.28/9.46      (![X0 : $i]:
% 9.28/9.46         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 9.28/9.46           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 9.28/9.46      inference('sup-', [status(thm)], ['32', '33'])).
% 9.28/9.46  thf('35', plain,
% 9.28/9.46      (((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 9.28/9.46            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 9.28/9.46      inference('demod', [status(thm)], ['27', '34'])).
% 9.28/9.46  thf('36', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 9.28/9.46         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 9.28/9.46      inference('sup+', [status(thm)], ['22', '35'])).
% 9.28/9.46  thf('37', plain,
% 9.28/9.46      (![X0 : $i]:
% 9.28/9.46         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 9.28/9.46           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 9.28/9.46      inference('sup-', [status(thm)], ['32', '33'])).
% 9.28/9.46  thf('38', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 9.28/9.46         <= (~
% 9.28/9.46             (((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 9.28/9.46      inference('split', [status(esa)], ['0'])).
% 9.28/9.46  thf('39', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 9.28/9.46         <= (~
% 9.28/9.46             (((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 9.28/9.46      inference('sup-', [status(thm)], ['37', '38'])).
% 9.28/9.46  thf('40', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 9.28/9.46         <= (~
% 9.28/9.46             (((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 9.28/9.46             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['36', '39'])).
% 9.28/9.46  thf('41', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 9.28/9.46       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 9.28/9.46      inference('simplify', [status(thm)], ['40'])).
% 9.28/9.46  thf('42', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 9.28/9.46       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 9.28/9.46      inference('split', [status(esa)], ['3'])).
% 9.28/9.46  thf('43', plain,
% 9.28/9.46      (((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 9.28/9.46      inference('demod', [status(thm)], ['25', '26'])).
% 9.28/9.46  thf('44', plain,
% 9.28/9.46      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 9.28/9.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('demod', [status(thm)], ['30', '31'])).
% 9.28/9.46  thf(dt_k7_subset_1, axiom,
% 9.28/9.46    (![A:$i,B:$i,C:$i]:
% 9.28/9.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.28/9.46       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.28/9.46  thf('45', plain,
% 9.28/9.46      (![X16 : $i, X17 : $i, X18 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 9.28/9.46          | (m1_subset_1 @ (k7_subset_1 @ X17 @ X16 @ X18) @ 
% 9.28/9.46             (k1_zfmisc_1 @ X17)))),
% 9.28/9.46      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 9.28/9.46  thf('46', plain,
% 9.28/9.46      (![X0 : $i]:
% 9.28/9.46         (m1_subset_1 @ 
% 9.28/9.46          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46           (k2_pre_topc @ sk_A @ sk_B_1) @ X0) @ 
% 9.28/9.46          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['44', '45'])).
% 9.28/9.46  thf('47', plain,
% 9.28/9.46      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 9.28/9.46        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('sup+', [status(thm)], ['43', '46'])).
% 9.28/9.46  thf('48', plain,
% 9.28/9.46      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf(redefinition_k4_subset_1, axiom,
% 9.28/9.46    (![A:$i,B:$i,C:$i]:
% 9.28/9.46     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 9.28/9.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 9.28/9.46       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 9.28/9.46  thf('49', plain,
% 9.28/9.46      (![X25 : $i, X26 : $i, X27 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 9.28/9.46          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 9.28/9.46          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 9.28/9.46      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 9.28/9.46  thf('50', plain,
% 9.28/9.46      (![X0 : $i]:
% 9.28/9.46         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 9.28/9.46            = (k2_xboole_0 @ sk_B_1 @ X0))
% 9.28/9.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 9.28/9.46      inference('sup-', [status(thm)], ['48', '49'])).
% 9.28/9.46  thf('51', plain,
% 9.28/9.46      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 9.28/9.46         (k2_tops_1 @ sk_A @ sk_B_1))
% 9.28/9.46         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['47', '50'])).
% 9.28/9.46  thf('52', plain,
% 9.28/9.46      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf(t65_tops_1, axiom,
% 9.28/9.46    (![A:$i]:
% 9.28/9.46     ( ( l1_pre_topc @ A ) =>
% 9.28/9.46       ( ![B:$i]:
% 9.28/9.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.28/9.46           ( ( k2_pre_topc @ A @ B ) =
% 9.28/9.46             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 9.28/9.46  thf('53', plain,
% 9.28/9.46      (![X50 : $i, X51 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 9.28/9.46          | ((k2_pre_topc @ X51 @ X50)
% 9.28/9.46              = (k4_subset_1 @ (u1_struct_0 @ X51) @ X50 @ 
% 9.28/9.46                 (k2_tops_1 @ X51 @ X50)))
% 9.28/9.46          | ~ (l1_pre_topc @ X51))),
% 9.28/9.46      inference('cnf', [status(esa)], [t65_tops_1])).
% 9.28/9.46  thf('54', plain,
% 9.28/9.46      ((~ (l1_pre_topc @ sk_A)
% 9.28/9.46        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 9.28/9.46            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 9.28/9.46               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 9.28/9.46      inference('sup-', [status(thm)], ['52', '53'])).
% 9.28/9.46  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('56', plain,
% 9.28/9.46      (((k2_pre_topc @ sk_A @ sk_B_1)
% 9.28/9.46         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 9.28/9.46            (k2_tops_1 @ sk_A @ sk_B_1)))),
% 9.28/9.46      inference('demod', [status(thm)], ['54', '55'])).
% 9.28/9.46  thf('57', plain,
% 9.28/9.46      (((k2_pre_topc @ sk_A @ sk_B_1)
% 9.28/9.46         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 9.28/9.46      inference('sup+', [status(thm)], ['51', '56'])).
% 9.28/9.46  thf(t46_xboole_1, axiom,
% 9.28/9.46    (![A:$i,B:$i]:
% 9.28/9.46     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 9.28/9.46  thf('58', plain,
% 9.28/9.46      (![X10 : $i, X11 : $i]:
% 9.28/9.46         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 9.28/9.46      inference('cnf', [status(esa)], [t46_xboole_1])).
% 9.28/9.46  thf(l32_xboole_1, axiom,
% 9.28/9.46    (![A:$i,B:$i]:
% 9.28/9.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.28/9.46  thf('59', plain,
% 9.28/9.46      (![X5 : $i, X6 : $i]:
% 9.28/9.46         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 9.28/9.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.28/9.46  thf('60', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         (((k1_xboole_0) != (k1_xboole_0))
% 9.28/9.46          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['58', '59'])).
% 9.28/9.46  thf('61', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 9.28/9.46      inference('simplify', [status(thm)], ['60'])).
% 9.28/9.46  thf(t3_subset, axiom,
% 9.28/9.46    (![A:$i,B:$i]:
% 9.28/9.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.28/9.46  thf('62', plain,
% 9.28/9.46      (![X36 : $i, X38 : $i]:
% 9.28/9.46         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 9.28/9.46      inference('cnf', [status(esa)], [t3_subset])).
% 9.28/9.46  thf('63', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['61', '62'])).
% 9.28/9.46  thf(d5_subset_1, axiom,
% 9.28/9.46    (![A:$i,B:$i]:
% 9.28/9.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.28/9.46       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 9.28/9.46  thf('64', plain,
% 9.28/9.46      (![X12 : $i, X13 : $i]:
% 9.28/9.46         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 9.28/9.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 9.28/9.46      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.28/9.46  thf('65', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 9.28/9.46           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 9.28/9.46      inference('sup-', [status(thm)], ['63', '64'])).
% 9.28/9.46  thf('66', plain,
% 9.28/9.46      (((k3_subset_1 @ (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 9.28/9.46         sk_B_1) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 9.28/9.46      inference('sup+', [status(thm)], ['57', '65'])).
% 9.28/9.46  thf('67', plain,
% 9.28/9.46      (((k2_pre_topc @ sk_A @ sk_B_1)
% 9.28/9.46         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 9.28/9.46      inference('sup+', [status(thm)], ['51', '56'])).
% 9.28/9.46  thf('68', plain,
% 9.28/9.46      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)
% 9.28/9.46         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))),
% 9.28/9.46      inference('demod', [status(thm)], ['66', '67'])).
% 9.28/9.46  thf('69', plain,
% 9.28/9.46      (![X0 : $i]:
% 9.28/9.46         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 9.28/9.46           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 9.28/9.46      inference('sup-', [status(thm)], ['32', '33'])).
% 9.28/9.46  thf('70', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 9.28/9.46         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 9.28/9.46      inference('split', [status(esa)], ['3'])).
% 9.28/9.46  thf('71', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 9.28/9.46         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 9.28/9.46      inference('sup+', [status(thm)], ['69', '70'])).
% 9.28/9.46  thf('72', plain,
% 9.28/9.46      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          = (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 9.28/9.46         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 9.28/9.46      inference('sup+', [status(thm)], ['68', '71'])).
% 9.28/9.46  thf('73', plain,
% 9.28/9.46      (((k2_pre_topc @ sk_A @ sk_B_1)
% 9.28/9.46         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 9.28/9.46      inference('sup+', [status(thm)], ['51', '56'])).
% 9.28/9.46  thf('74', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['61', '62'])).
% 9.28/9.46  thf('75', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['61', '62'])).
% 9.28/9.46  thf(dt_k3_subset_1, axiom,
% 9.28/9.46    (![A:$i,B:$i]:
% 9.28/9.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.28/9.46       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 9.28/9.46  thf('76', plain,
% 9.28/9.46      (![X14 : $i, X15 : $i]:
% 9.28/9.46         ((m1_subset_1 @ (k3_subset_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 9.28/9.46          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 9.28/9.46      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 9.28/9.46  thf('77', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         (m1_subset_1 @ (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 9.28/9.46          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['75', '76'])).
% 9.28/9.46  thf(t32_subset_1, axiom,
% 9.28/9.46    (![A:$i,B:$i]:
% 9.28/9.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.28/9.46       ( ![C:$i]:
% 9.28/9.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.28/9.46           ( ( k7_subset_1 @ A @ B @ C ) =
% 9.28/9.46             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 9.28/9.46  thf('78', plain,
% 9.28/9.46      (![X31 : $i, X32 : $i, X33 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 9.28/9.46          | ((k7_subset_1 @ X32 @ X33 @ X31)
% 9.28/9.46              = (k9_subset_1 @ X32 @ X33 @ (k3_subset_1 @ X32 @ X31)))
% 9.28/9.46          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 9.28/9.46      inference('cnf', [status(esa)], [t32_subset_1])).
% 9.28/9.46  thf('79', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 9.28/9.46          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 9.28/9.46              (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 9.28/9.46              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 9.28/9.46                 (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 9.28/9.46                  (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)))))),
% 9.28/9.46      inference('sup-', [status(thm)], ['77', '78'])).
% 9.28/9.46  thf('80', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['61', '62'])).
% 9.28/9.46  thf(involutiveness_k3_subset_1, axiom,
% 9.28/9.46    (![A:$i,B:$i]:
% 9.28/9.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.28/9.46       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 9.28/9.46  thf('81', plain,
% 9.28/9.46      (![X23 : $i, X24 : $i]:
% 9.28/9.46         (((k3_subset_1 @ X24 @ (k3_subset_1 @ X24 @ X23)) = (X23))
% 9.28/9.46          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 9.28/9.46      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.28/9.46  thf('82', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 9.28/9.46           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 9.28/9.46      inference('sup-', [status(thm)], ['80', '81'])).
% 9.28/9.46  thf('83', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 9.28/9.46          | ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ 
% 9.28/9.46              (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 9.28/9.46              = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X2 @ X1)))),
% 9.28/9.46      inference('demod', [status(thm)], ['79', '82'])).
% 9.28/9.46  thf('84', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ 
% 9.28/9.46           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 9.28/9.46           = (k9_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ X1))),
% 9.28/9.46      inference('sup-', [status(thm)], ['74', '83'])).
% 9.28/9.46  thf('85', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.28/9.46      inference('sup-', [status(thm)], ['61', '62'])).
% 9.28/9.46  thf('86', plain,
% 9.28/9.46      (![X28 : $i, X29 : $i, X30 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 9.28/9.46          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 9.28/9.46      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 9.28/9.46  thf('87', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.28/9.46         ((k7_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1 @ X2)
% 9.28/9.46           = (k4_xboole_0 @ X1 @ X2))),
% 9.28/9.46      inference('sup-', [status(thm)], ['85', '86'])).
% 9.28/9.46  thf('88', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 9.28/9.46      inference('simplify', [status(thm)], ['12'])).
% 9.28/9.46  thf('89', plain,
% 9.28/9.46      (![X36 : $i, X38 : $i]:
% 9.28/9.46         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X38)) | ~ (r1_tarski @ X36 @ X38))),
% 9.28/9.46      inference('cnf', [status(esa)], [t3_subset])).
% 9.28/9.46  thf('90', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 9.28/9.46      inference('sup-', [status(thm)], ['88', '89'])).
% 9.28/9.46  thf(idempotence_k9_subset_1, axiom,
% 9.28/9.46    (![A:$i,B:$i,C:$i]:
% 9.28/9.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 9.28/9.46       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 9.28/9.46  thf('91', plain,
% 9.28/9.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 9.28/9.46         (((k9_subset_1 @ X21 @ X20 @ X20) = (X20))
% 9.28/9.46          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 9.28/9.46      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 9.28/9.46  thf('92', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 9.28/9.46      inference('sup-', [status(thm)], ['90', '91'])).
% 9.28/9.46  thf('93', plain,
% 9.28/9.46      (![X0 : $i, X1 : $i]:
% 9.28/9.46         ((k4_xboole_0 @ X1 @ (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 9.28/9.46           = (X1))),
% 9.28/9.46      inference('demod', [status(thm)], ['84', '87', '92'])).
% 9.28/9.46  thf('94', plain,
% 9.28/9.46      (((k4_xboole_0 @ sk_B_1 @ 
% 9.28/9.46         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 9.28/9.46      inference('sup+', [status(thm)], ['73', '93'])).
% 9.28/9.46  thf('95', plain,
% 9.28/9.46      ((((k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 9.28/9.46         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 9.28/9.46      inference('sup+', [status(thm)], ['72', '94'])).
% 9.28/9.46  thf('96', plain,
% 9.28/9.46      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf(t74_tops_1, axiom,
% 9.28/9.46    (![A:$i]:
% 9.28/9.46     ( ( l1_pre_topc @ A ) =>
% 9.28/9.46       ( ![B:$i]:
% 9.28/9.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.28/9.46           ( ( k1_tops_1 @ A @ B ) =
% 9.28/9.46             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 9.28/9.46  thf('97', plain,
% 9.28/9.46      (![X52 : $i, X53 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 9.28/9.46          | ((k1_tops_1 @ X53 @ X52)
% 9.28/9.46              = (k7_subset_1 @ (u1_struct_0 @ X53) @ X52 @ 
% 9.28/9.46                 (k2_tops_1 @ X53 @ X52)))
% 9.28/9.46          | ~ (l1_pre_topc @ X53))),
% 9.28/9.46      inference('cnf', [status(esa)], [t74_tops_1])).
% 9.28/9.46  thf('98', plain,
% 9.28/9.46      ((~ (l1_pre_topc @ sk_A)
% 9.28/9.46        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 9.28/9.46               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 9.28/9.46      inference('sup-', [status(thm)], ['96', '97'])).
% 9.28/9.46  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('100', plain,
% 9.28/9.46      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('101', plain,
% 9.28/9.46      (![X28 : $i, X29 : $i, X30 : $i]:
% 9.28/9.46         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 9.28/9.46          | ((k7_subset_1 @ X29 @ X28 @ X30) = (k4_xboole_0 @ X28 @ X30)))),
% 9.28/9.46      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 9.28/9.46  thf('102', plain,
% 9.28/9.46      (![X0 : $i]:
% 9.28/9.46         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 9.28/9.46           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 9.28/9.46      inference('sup-', [status(thm)], ['100', '101'])).
% 9.28/9.46  thf('103', plain,
% 9.28/9.46      (((k1_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 9.28/9.46      inference('demod', [status(thm)], ['98', '99', '102'])).
% 9.28/9.46  thf('104', plain,
% 9.28/9.46      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 9.28/9.46         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 9.28/9.46      inference('sup+', [status(thm)], ['95', '103'])).
% 9.28/9.46  thf('105', plain,
% 9.28/9.46      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf(fc9_tops_1, axiom,
% 9.28/9.46    (![A:$i,B:$i]:
% 9.28/9.46     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 9.28/9.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 9.28/9.46       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 9.28/9.46  thf('106', plain,
% 9.28/9.46      (![X41 : $i, X42 : $i]:
% 9.28/9.46         (~ (l1_pre_topc @ X41)
% 9.28/9.46          | ~ (v2_pre_topc @ X41)
% 9.28/9.46          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41)))
% 9.28/9.46          | (v3_pre_topc @ (k1_tops_1 @ X41 @ X42) @ X41))),
% 9.28/9.46      inference('cnf', [status(esa)], [fc9_tops_1])).
% 9.28/9.46  thf('107', plain,
% 9.28/9.46      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 9.28/9.46        | ~ (v2_pre_topc @ sk_A)
% 9.28/9.46        | ~ (l1_pre_topc @ sk_A))),
% 9.28/9.46      inference('sup-', [status(thm)], ['105', '106'])).
% 9.28/9.46  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 9.28/9.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.28/9.46  thf('110', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 9.28/9.46      inference('demod', [status(thm)], ['107', '108', '109'])).
% 9.28/9.46  thf('111', plain,
% 9.28/9.46      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 9.28/9.46         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 9.28/9.46      inference('sup+', [status(thm)], ['104', '110'])).
% 9.28/9.46  thf('112', plain,
% 9.28/9.46      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 9.28/9.46      inference('split', [status(esa)], ['0'])).
% 9.28/9.46  thf('113', plain,
% 9.28/9.46      (~
% 9.28/9.46       (((k2_tops_1 @ sk_A @ sk_B_1)
% 9.28/9.46          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.28/9.46             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 9.28/9.46       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 9.28/9.46      inference('sup-', [status(thm)], ['111', '112'])).
% 9.28/9.46  thf('114', plain, ($false),
% 9.28/9.46      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '113'])).
% 9.28/9.46  
% 9.28/9.46  % SZS output end Refutation
% 9.28/9.46  
% 9.28/9.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
