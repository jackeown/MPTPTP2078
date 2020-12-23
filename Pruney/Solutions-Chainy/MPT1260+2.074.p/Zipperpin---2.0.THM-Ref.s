%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gmnLnOLJ85

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:34 EST 2020

% Result     : Theorem 35.75s
% Output     : Refutation 35.75s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 840 expanded)
%              Number of leaves         :   36 ( 254 expanded)
%              Depth                    :   15
%              Number of atoms          : 1647 (11739 expanded)
%              Number of equality atoms :   96 ( 513 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v3_pre_topc @ X44 @ X45 )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r1_tarski @ X44 @ ( k1_tops_1 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
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
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k1_tops_1 @ X50 @ X49 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 @ ( k2_tops_1 @ X50 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k2_tops_1 @ X43 @ X42 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k2_pre_topc @ X43 @ X42 ) @ ( k1_tops_1 @ X43 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('37',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('46',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k4_subset_1 @ X25 @ X24 @ X26 )
        = ( k2_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( ( k2_pre_topc @ X48 @ X47 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X48 ) @ X47 @ ( k2_tops_1 @ X48 @ X47 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('55',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('57',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['34','58'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('62',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      & ( v3_pre_topc @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('68',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('71',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('74',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k7_subset_1 @ X31 @ X32 @ X30 )
        = ( k9_subset_1 @ X31 @ X32 @ ( k3_subset_1 @ X31 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('82',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('86',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('88',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X19 @ X18 @ X18 )
        = X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,
    ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['69','90'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('93',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('94',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('95',plain,(
    ! [X35: $i,X37: $i] :
      ( ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('97',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X22 @ ( k3_subset_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('100',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['98','101','102'])).

thf('104',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['93','103'])).

thf('105',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('106',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['92','106'])).

thf('108',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('109',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('110',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['92','106'])).

thf('111',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['91','107','108','109','110'])).

thf('112',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('113',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = sk_B_1 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('115',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X40 @ X41 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('116',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['113','119'])).

thf('121',plain,
    ( ~ ( v3_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('122',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_B_1 ) )
    | ( v3_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','65','66','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gmnLnOLJ85
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:28:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 35.75/36.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 35.75/36.01  % Solved by: fo/fo7.sh
% 35.75/36.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 35.75/36.01  % done 17974 iterations in 35.555s
% 35.75/36.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 35.75/36.01  % SZS output start Refutation
% 35.75/36.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 35.75/36.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 35.75/36.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 35.75/36.01  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 35.75/36.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 35.75/36.01  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 35.75/36.01  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 35.75/36.01  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 35.75/36.01  thf(sk_A_type, type, sk_A: $i).
% 35.75/36.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 35.75/36.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 35.75/36.01  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 35.75/36.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 35.75/36.01  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 35.75/36.01  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 35.75/36.01  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 35.75/36.01  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 35.75/36.01  thf(sk_B_1_type, type, sk_B_1: $i).
% 35.75/36.01  thf(t76_tops_1, conjecture,
% 35.75/36.01    (![A:$i]:
% 35.75/36.01     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 35.75/36.01       ( ![B:$i]:
% 35.75/36.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 35.75/36.01           ( ( v3_pre_topc @ B @ A ) <=>
% 35.75/36.01             ( ( k2_tops_1 @ A @ B ) =
% 35.75/36.01               ( k7_subset_1 @
% 35.75/36.01                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 35.75/36.01  thf(zf_stmt_0, negated_conjecture,
% 35.75/36.01    (~( ![A:$i]:
% 35.75/36.01        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 35.75/36.01          ( ![B:$i]:
% 35.75/36.01            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 35.75/36.01              ( ( v3_pre_topc @ B @ A ) <=>
% 35.75/36.01                ( ( k2_tops_1 @ A @ B ) =
% 35.75/36.01                  ( k7_subset_1 @
% 35.75/36.01                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 35.75/36.01    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 35.75/36.01  thf('0', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 35.75/36.01        | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf('1', plain,
% 35.75/36.01      (~
% 35.75/36.01       (((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 35.75/36.01       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 35.75/36.01      inference('split', [status(esa)], ['0'])).
% 35.75/36.01  thf('2', plain,
% 35.75/36.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf('3', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 35.75/36.01        | (v3_pre_topc @ sk_B_1 @ sk_A))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf('4', plain,
% 35.75/36.01      (((v3_pre_topc @ sk_B_1 @ sk_A)) <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 35.75/36.01      inference('split', [status(esa)], ['3'])).
% 35.75/36.01  thf('5', plain,
% 35.75/36.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf(t56_tops_1, axiom,
% 35.75/36.01    (![A:$i]:
% 35.75/36.01     ( ( l1_pre_topc @ A ) =>
% 35.75/36.01       ( ![B:$i]:
% 35.75/36.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 35.75/36.01           ( ![C:$i]:
% 35.75/36.01             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 35.75/36.01               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 35.75/36.01                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 35.75/36.01  thf('6', plain,
% 35.75/36.01      (![X44 : $i, X45 : $i, X46 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 35.75/36.01          | ~ (v3_pre_topc @ X44 @ X45)
% 35.75/36.01          | ~ (r1_tarski @ X44 @ X46)
% 35.75/36.01          | (r1_tarski @ X44 @ (k1_tops_1 @ X45 @ X46))
% 35.75/36.01          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 35.75/36.01          | ~ (l1_pre_topc @ X45))),
% 35.75/36.01      inference('cnf', [status(esa)], [t56_tops_1])).
% 35.75/36.01  thf('7', plain,
% 35.75/36.01      (![X0 : $i]:
% 35.75/36.01         (~ (l1_pre_topc @ sk_A)
% 35.75/36.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 35.75/36.01          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 35.75/36.01          | ~ (r1_tarski @ sk_B_1 @ X0)
% 35.75/36.01          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 35.75/36.01      inference('sup-', [status(thm)], ['5', '6'])).
% 35.75/36.01  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf('9', plain,
% 35.75/36.01      (![X0 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 35.75/36.01          | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 35.75/36.01          | ~ (r1_tarski @ sk_B_1 @ X0)
% 35.75/36.01          | ~ (v3_pre_topc @ sk_B_1 @ sk_A))),
% 35.75/36.01      inference('demod', [status(thm)], ['7', '8'])).
% 35.75/36.01  thf('10', plain,
% 35.75/36.01      ((![X0 : $i]:
% 35.75/36.01          (~ (r1_tarski @ sk_B_1 @ X0)
% 35.75/36.01           | (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ X0))
% 35.75/36.01           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 35.75/36.01         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['4', '9'])).
% 35.75/36.01  thf('11', plain,
% 35.75/36.01      ((((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 35.75/36.01         | ~ (r1_tarski @ sk_B_1 @ sk_B_1)))
% 35.75/36.01         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['2', '10'])).
% 35.75/36.01  thf(d10_xboole_0, axiom,
% 35.75/36.01    (![A:$i,B:$i]:
% 35.75/36.01     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 35.75/36.01  thf('12', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 35.75/36.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 35.75/36.01  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 35.75/36.01      inference('simplify', [status(thm)], ['12'])).
% 35.75/36.01  thf('14', plain,
% 35.75/36.01      (((r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 35.75/36.01         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 35.75/36.01      inference('demod', [status(thm)], ['11', '13'])).
% 35.75/36.01  thf('15', plain,
% 35.75/36.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf(t74_tops_1, axiom,
% 35.75/36.01    (![A:$i]:
% 35.75/36.01     ( ( l1_pre_topc @ A ) =>
% 35.75/36.01       ( ![B:$i]:
% 35.75/36.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 35.75/36.01           ( ( k1_tops_1 @ A @ B ) =
% 35.75/36.01             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 35.75/36.01  thf('16', plain,
% 35.75/36.01      (![X49 : $i, X50 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 35.75/36.01          | ((k1_tops_1 @ X50 @ X49)
% 35.75/36.01              = (k7_subset_1 @ (u1_struct_0 @ X50) @ X49 @ 
% 35.75/36.01                 (k2_tops_1 @ X50 @ X49)))
% 35.75/36.01          | ~ (l1_pre_topc @ X50))),
% 35.75/36.01      inference('cnf', [status(esa)], [t74_tops_1])).
% 35.75/36.01  thf('17', plain,
% 35.75/36.01      ((~ (l1_pre_topc @ sk_A)
% 35.75/36.01        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 35.75/36.01               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 35.75/36.01      inference('sup-', [status(thm)], ['15', '16'])).
% 35.75/36.01  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf('19', plain,
% 35.75/36.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf(redefinition_k7_subset_1, axiom,
% 35.75/36.01    (![A:$i,B:$i,C:$i]:
% 35.75/36.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 35.75/36.01       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 35.75/36.01  thf('20', plain,
% 35.75/36.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 35.75/36.01          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 35.75/36.01      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 35.75/36.01  thf('21', plain,
% 35.75/36.01      (![X0 : $i]:
% 35.75/36.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 35.75/36.01           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 35.75/36.01      inference('sup-', [status(thm)], ['19', '20'])).
% 35.75/36.01  thf('22', plain,
% 35.75/36.01      (((k1_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('demod', [status(thm)], ['17', '18', '21'])).
% 35.75/36.01  thf(t36_xboole_1, axiom,
% 35.75/36.01    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 35.75/36.01  thf('23', plain,
% 35.75/36.01      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 35.75/36.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 35.75/36.01  thf('24', plain,
% 35.75/36.01      (![X0 : $i, X2 : $i]:
% 35.75/36.01         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 35.75/36.01      inference('cnf', [status(esa)], [d10_xboole_0])).
% 35.75/36.01  thf('25', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 35.75/36.01          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['23', '24'])).
% 35.75/36.01  thf('26', plain,
% 35.75/36.01      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 35.75/36.01        | ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 35.75/36.01      inference('sup-', [status(thm)], ['22', '25'])).
% 35.75/36.01  thf('27', plain,
% 35.75/36.01      (((k1_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('demod', [status(thm)], ['17', '18', '21'])).
% 35.75/36.01  thf('28', plain,
% 35.75/36.01      ((~ (r1_tarski @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 35.75/36.01        | ((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('demod', [status(thm)], ['26', '27'])).
% 35.75/36.01  thf('29', plain,
% 35.75/36.01      ((((sk_B_1) = (k1_tops_1 @ sk_A @ sk_B_1)))
% 35.75/36.01         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['14', '28'])).
% 35.75/36.01  thf('30', plain,
% 35.75/36.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf(l78_tops_1, axiom,
% 35.75/36.01    (![A:$i]:
% 35.75/36.01     ( ( l1_pre_topc @ A ) =>
% 35.75/36.01       ( ![B:$i]:
% 35.75/36.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 35.75/36.01           ( ( k2_tops_1 @ A @ B ) =
% 35.75/36.01             ( k7_subset_1 @
% 35.75/36.01               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 35.75/36.01               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 35.75/36.01  thf('31', plain,
% 35.75/36.01      (![X42 : $i, X43 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 35.75/36.01          | ((k2_tops_1 @ X43 @ X42)
% 35.75/36.01              = (k7_subset_1 @ (u1_struct_0 @ X43) @ 
% 35.75/36.01                 (k2_pre_topc @ X43 @ X42) @ (k1_tops_1 @ X43 @ X42)))
% 35.75/36.01          | ~ (l1_pre_topc @ X43))),
% 35.75/36.01      inference('cnf', [status(esa)], [l78_tops_1])).
% 35.75/36.01  thf('32', plain,
% 35.75/36.01      ((~ (l1_pre_topc @ sk_A)
% 35.75/36.01        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 35.75/36.01      inference('sup-', [status(thm)], ['30', '31'])).
% 35.75/36.01  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf('34', plain,
% 35.75/36.01      (((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01            (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('demod', [status(thm)], ['32', '33'])).
% 35.75/36.01  thf('35', plain,
% 35.75/36.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf(dt_k2_tops_1, axiom,
% 35.75/36.01    (![A:$i,B:$i]:
% 35.75/36.01     ( ( ( l1_pre_topc @ A ) & 
% 35.75/36.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 35.75/36.01       ( m1_subset_1 @
% 35.75/36.01         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 35.75/36.01  thf('36', plain,
% 35.75/36.01      (![X38 : $i, X39 : $i]:
% 35.75/36.01         (~ (l1_pre_topc @ X38)
% 35.75/36.01          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 35.75/36.01          | (m1_subset_1 @ (k2_tops_1 @ X38 @ X39) @ 
% 35.75/36.01             (k1_zfmisc_1 @ (u1_struct_0 @ X38))))),
% 35.75/36.01      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 35.75/36.01  thf('37', plain,
% 35.75/36.01      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 35.75/36.01         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 35.75/36.01        | ~ (l1_pre_topc @ sk_A))),
% 35.75/36.01      inference('sup-', [status(thm)], ['35', '36'])).
% 35.75/36.01  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf('39', plain,
% 35.75/36.01      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 35.75/36.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('demod', [status(thm)], ['37', '38'])).
% 35.75/36.01  thf('40', plain,
% 35.75/36.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf(dt_k4_subset_1, axiom,
% 35.75/36.01    (![A:$i,B:$i,C:$i]:
% 35.75/36.01     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 35.75/36.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 35.75/36.01       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 35.75/36.01  thf('41', plain,
% 35.75/36.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 35.75/36.01          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 35.75/36.01          | (m1_subset_1 @ (k4_subset_1 @ X16 @ X15 @ X17) @ 
% 35.75/36.01             (k1_zfmisc_1 @ X16)))),
% 35.75/36.01      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 35.75/36.01  thf('42', plain,
% 35.75/36.01      (![X0 : $i]:
% 35.75/36.01         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 35.75/36.01           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 35.75/36.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 35.75/36.01      inference('sup-', [status(thm)], ['40', '41'])).
% 35.75/36.01  thf('43', plain,
% 35.75/36.01      ((m1_subset_1 @ 
% 35.75/36.01        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 35.75/36.01         (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 35.75/36.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['39', '42'])).
% 35.75/36.01  thf('44', plain,
% 35.75/36.01      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B_1) @ 
% 35.75/36.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('demod', [status(thm)], ['37', '38'])).
% 35.75/36.01  thf('45', plain,
% 35.75/36.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf(redefinition_k4_subset_1, axiom,
% 35.75/36.01    (![A:$i,B:$i,C:$i]:
% 35.75/36.01     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 35.75/36.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 35.75/36.01       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 35.75/36.01  thf('46', plain,
% 35.75/36.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 35.75/36.01          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25))
% 35.75/36.01          | ((k4_subset_1 @ X25 @ X24 @ X26) = (k2_xboole_0 @ X24 @ X26)))),
% 35.75/36.01      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 35.75/36.01  thf('47', plain,
% 35.75/36.01      (![X0 : $i]:
% 35.75/36.01         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 35.75/36.01            = (k2_xboole_0 @ sk_B_1 @ X0))
% 35.75/36.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 35.75/36.01      inference('sup-', [status(thm)], ['45', '46'])).
% 35.75/36.01  thf('48', plain,
% 35.75/36.01      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 35.75/36.01         (k2_tops_1 @ sk_A @ sk_B_1))
% 35.75/36.01         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['44', '47'])).
% 35.75/36.01  thf('49', plain,
% 35.75/36.01      ((m1_subset_1 @ (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 35.75/36.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('demod', [status(thm)], ['43', '48'])).
% 35.75/36.01  thf('50', plain,
% 35.75/36.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf(t65_tops_1, axiom,
% 35.75/36.01    (![A:$i]:
% 35.75/36.01     ( ( l1_pre_topc @ A ) =>
% 35.75/36.01       ( ![B:$i]:
% 35.75/36.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 35.75/36.01           ( ( k2_pre_topc @ A @ B ) =
% 35.75/36.01             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 35.75/36.01  thf('51', plain,
% 35.75/36.01      (![X47 : $i, X48 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 35.75/36.01          | ((k2_pre_topc @ X48 @ X47)
% 35.75/36.01              = (k4_subset_1 @ (u1_struct_0 @ X48) @ X47 @ 
% 35.75/36.01                 (k2_tops_1 @ X48 @ X47)))
% 35.75/36.01          | ~ (l1_pre_topc @ X48))),
% 35.75/36.01      inference('cnf', [status(esa)], [t65_tops_1])).
% 35.75/36.01  thf('52', plain,
% 35.75/36.01      ((~ (l1_pre_topc @ sk_A)
% 35.75/36.01        | ((k2_pre_topc @ sk_A @ sk_B_1)
% 35.75/36.01            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 35.75/36.01               (k2_tops_1 @ sk_A @ sk_B_1))))),
% 35.75/36.01      inference('sup-', [status(thm)], ['50', '51'])).
% 35.75/36.01  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf('54', plain,
% 35.75/36.01      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 35.75/36.01         (k2_tops_1 @ sk_A @ sk_B_1))
% 35.75/36.01         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['44', '47'])).
% 35.75/36.01  thf('55', plain,
% 35.75/36.01      (((k2_pre_topc @ sk_A @ sk_B_1)
% 35.75/36.01         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('demod', [status(thm)], ['52', '53', '54'])).
% 35.75/36.01  thf('56', plain,
% 35.75/36.01      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 35.75/36.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('demod', [status(thm)], ['49', '55'])).
% 35.75/36.01  thf('57', plain,
% 35.75/36.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 35.75/36.01          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 35.75/36.01      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 35.75/36.01  thf('58', plain,
% 35.75/36.01      (![X0 : $i]:
% 35.75/36.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 35.75/36.01           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 35.75/36.01      inference('sup-', [status(thm)], ['56', '57'])).
% 35.75/36.01  thf('59', plain,
% 35.75/36.01      (((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 35.75/36.01            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('demod', [status(thm)], ['34', '58'])).
% 35.75/36.01  thf('60', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 35.75/36.01         <= (((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 35.75/36.01      inference('sup+', [status(thm)], ['29', '59'])).
% 35.75/36.01  thf('61', plain,
% 35.75/36.01      (![X0 : $i]:
% 35.75/36.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 35.75/36.01           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 35.75/36.01      inference('sup-', [status(thm)], ['56', '57'])).
% 35.75/36.01  thf('62', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01              (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 35.75/36.01         <= (~
% 35.75/36.01             (((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('split', [status(esa)], ['0'])).
% 35.75/36.01  thf('63', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 35.75/36.01         <= (~
% 35.75/36.01             (((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('sup-', [status(thm)], ['61', '62'])).
% 35.75/36.01  thf('64', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1) != (k2_tops_1 @ sk_A @ sk_B_1)))
% 35.75/36.01         <= (~
% 35.75/36.01             (((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) & 
% 35.75/36.01             ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['60', '63'])).
% 35.75/36.01  thf('65', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 35.75/36.01       ~ ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 35.75/36.01      inference('simplify', [status(thm)], ['64'])).
% 35.75/36.01  thf('66', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 35.75/36.01       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 35.75/36.01      inference('split', [status(esa)], ['3'])).
% 35.75/36.01  thf('67', plain,
% 35.75/36.01      (![X0 : $i]:
% 35.75/36.01         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 35.75/36.01           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 35.75/36.01      inference('sup-', [status(thm)], ['56', '57'])).
% 35.75/36.01  thf('68', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('split', [status(esa)], ['3'])).
% 35.75/36.01  thf('69', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('sup+', [status(thm)], ['67', '68'])).
% 35.75/36.01  thf('70', plain,
% 35.75/36.01      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 35.75/36.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 35.75/36.01  thf(t3_subset, axiom,
% 35.75/36.01    (![A:$i,B:$i]:
% 35.75/36.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 35.75/36.01  thf('71', plain,
% 35.75/36.01      (![X35 : $i, X37 : $i]:
% 35.75/36.01         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 35.75/36.01      inference('cnf', [status(esa)], [t3_subset])).
% 35.75/36.01  thf('72', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 35.75/36.01      inference('sup-', [status(thm)], ['70', '71'])).
% 35.75/36.01  thf('73', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 35.75/36.01      inference('sup-', [status(thm)], ['70', '71'])).
% 35.75/36.01  thf(t32_subset_1, axiom,
% 35.75/36.01    (![A:$i,B:$i]:
% 35.75/36.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 35.75/36.01       ( ![C:$i]:
% 35.75/36.01         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 35.75/36.01           ( ( k7_subset_1 @ A @ B @ C ) =
% 35.75/36.01             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 35.75/36.01  thf('74', plain,
% 35.75/36.01      (![X30 : $i, X31 : $i, X32 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 35.75/36.01          | ((k7_subset_1 @ X31 @ X32 @ X30)
% 35.75/36.01              = (k9_subset_1 @ X31 @ X32 @ (k3_subset_1 @ X31 @ X30)))
% 35.75/36.01          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 35.75/36.01      inference('cnf', [status(esa)], [t32_subset_1])).
% 35.75/36.01  thf('75', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 35.75/36.01          | ((k7_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 35.75/36.01              = (k9_subset_1 @ X0 @ X2 @ 
% 35.75/36.01                 (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))))),
% 35.75/36.01      inference('sup-', [status(thm)], ['73', '74'])).
% 35.75/36.01  thf('76', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 35.75/36.01      inference('sup-', [status(thm)], ['70', '71'])).
% 35.75/36.01  thf(d5_subset_1, axiom,
% 35.75/36.01    (![A:$i,B:$i]:
% 35.75/36.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 35.75/36.01       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 35.75/36.01  thf('77', plain,
% 35.75/36.01      (![X11 : $i, X12 : $i]:
% 35.75/36.01         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 35.75/36.01          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 35.75/36.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 35.75/36.01  thf('78', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 35.75/36.01           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['76', '77'])).
% 35.75/36.01  thf('79', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 35.75/36.01          | ((k7_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 35.75/36.01              = (k9_subset_1 @ X0 @ X2 @ 
% 35.75/36.01                 (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))))),
% 35.75/36.01      inference('demod', [status(thm)], ['75', '78'])).
% 35.75/36.01  thf('80', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.75/36.01         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2))
% 35.75/36.01           = (k9_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 35.75/36.01              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2))))),
% 35.75/36.01      inference('sup-', [status(thm)], ['72', '79'])).
% 35.75/36.01  thf('81', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 35.75/36.01      inference('sup-', [status(thm)], ['70', '71'])).
% 35.75/36.01  thf('82', plain,
% 35.75/36.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 35.75/36.01         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 35.75/36.01          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 35.75/36.01      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 35.75/36.01  thf('83', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.75/36.01         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 35.75/36.01           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 35.75/36.01      inference('sup-', [status(thm)], ['81', '82'])).
% 35.75/36.01  thf('84', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 35.75/36.01         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2))
% 35.75/36.01           = (k9_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 35.75/36.01              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2))))),
% 35.75/36.01      inference('demod', [status(thm)], ['80', '83'])).
% 35.75/36.01  thf('85', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 35.75/36.01      inference('simplify', [status(thm)], ['12'])).
% 35.75/36.01  thf('86', plain,
% 35.75/36.01      (![X35 : $i, X37 : $i]:
% 35.75/36.01         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 35.75/36.01      inference('cnf', [status(esa)], [t3_subset])).
% 35.75/36.01  thf('87', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 35.75/36.01      inference('sup-', [status(thm)], ['85', '86'])).
% 35.75/36.01  thf(idempotence_k9_subset_1, axiom,
% 35.75/36.01    (![A:$i,B:$i,C:$i]:
% 35.75/36.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 35.75/36.01       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 35.75/36.01  thf('88', plain,
% 35.75/36.01      (![X18 : $i, X19 : $i, X20 : $i]:
% 35.75/36.01         (((k9_subset_1 @ X19 @ X18 @ X18) = (X18))
% 35.75/36.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 35.75/36.01      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 35.75/36.01  thf('89', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 35.75/36.01      inference('sup-', [status(thm)], ['87', '88'])).
% 35.75/36.01  thf('90', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 35.75/36.01           (k4_xboole_0 @ X1 @ X0))
% 35.75/36.01           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 35.75/36.01      inference('sup+', [status(thm)], ['84', '89'])).
% 35.75/36.01  thf('91', plain,
% 35.75/36.01      ((((k4_xboole_0 @ 
% 35.75/36.01          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 35.75/36.01           (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 35.75/36.01          (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))
% 35.75/36.01          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 35.75/36.01             (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('sup+', [status(thm)], ['69', '90'])).
% 35.75/36.01  thf('92', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('sup+', [status(thm)], ['67', '68'])).
% 35.75/36.01  thf('93', plain,
% 35.75/36.01      (((k2_pre_topc @ sk_A @ sk_B_1)
% 35.75/36.01         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('demod', [status(thm)], ['52', '53', '54'])).
% 35.75/36.01  thf(t7_xboole_1, axiom,
% 35.75/36.01    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 35.75/36.01  thf('94', plain,
% 35.75/36.01      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 35.75/36.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 35.75/36.01  thf('95', plain,
% 35.75/36.01      (![X35 : $i, X37 : $i]:
% 35.75/36.01         ((m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X37)) | ~ (r1_tarski @ X35 @ X37))),
% 35.75/36.01      inference('cnf', [status(esa)], [t3_subset])).
% 35.75/36.01  thf('96', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['94', '95'])).
% 35.75/36.01  thf(involutiveness_k3_subset_1, axiom,
% 35.75/36.01    (![A:$i,B:$i]:
% 35.75/36.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 35.75/36.01       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 35.75/36.01  thf('97', plain,
% 35.75/36.01      (![X21 : $i, X22 : $i]:
% 35.75/36.01         (((k3_subset_1 @ X22 @ (k3_subset_1 @ X22 @ X21)) = (X21))
% 35.75/36.01          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 35.75/36.01      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 35.75/36.01  thf('98', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 35.75/36.01           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 35.75/36.01      inference('sup-', [status(thm)], ['96', '97'])).
% 35.75/36.01  thf('99', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['94', '95'])).
% 35.75/36.01  thf('100', plain,
% 35.75/36.01      (![X11 : $i, X12 : $i]:
% 35.75/36.01         (((k3_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))
% 35.75/36.01          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 35.75/36.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 35.75/36.01  thf('101', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 35.75/36.01           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 35.75/36.01      inference('sup-', [status(thm)], ['99', '100'])).
% 35.75/36.01  thf('102', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 35.75/36.01           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 35.75/36.01      inference('sup-', [status(thm)], ['76', '77'])).
% 35.75/36.01  thf('103', plain,
% 35.75/36.01      (![X0 : $i, X1 : $i]:
% 35.75/36.01         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 35.75/36.01           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)) = (X1))),
% 35.75/36.01      inference('demod', [status(thm)], ['98', '101', '102'])).
% 35.75/36.01  thf('104', plain,
% 35.75/36.01      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) @ 
% 35.75/36.01         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 35.75/36.01      inference('sup+', [status(thm)], ['93', '103'])).
% 35.75/36.01  thf('105', plain,
% 35.75/36.01      (((k2_pre_topc @ sk_A @ sk_B_1)
% 35.75/36.01         = (k2_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('demod', [status(thm)], ['52', '53', '54'])).
% 35.75/36.01  thf('106', plain,
% 35.75/36.01      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 35.75/36.01         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)) = (sk_B_1))),
% 35.75/36.01      inference('demod', [status(thm)], ['104', '105'])).
% 35.75/36.01  thf('107', plain,
% 35.75/36.01      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 35.75/36.01          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('sup+', [status(thm)], ['92', '106'])).
% 35.75/36.01  thf('108', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('sup+', [status(thm)], ['67', '68'])).
% 35.75/36.01  thf('109', plain,
% 35.75/36.01      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1)))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('sup+', [status(thm)], ['67', '68'])).
% 35.75/36.01  thf('110', plain,
% 35.75/36.01      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 35.75/36.01          (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('sup+', [status(thm)], ['92', '106'])).
% 35.75/36.01  thf('111', plain,
% 35.75/36.01      ((((k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)) = (sk_B_1)))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('demod', [status(thm)], ['91', '107', '108', '109', '110'])).
% 35.75/36.01  thf('112', plain,
% 35.75/36.01      (((k1_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01         = (k4_xboole_0 @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))),
% 35.75/36.01      inference('demod', [status(thm)], ['17', '18', '21'])).
% 35.75/36.01  thf('113', plain,
% 35.75/36.01      ((((k1_tops_1 @ sk_A @ sk_B_1) = (sk_B_1)))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('sup+', [status(thm)], ['111', '112'])).
% 35.75/36.01  thf('114', plain,
% 35.75/36.01      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf(fc9_tops_1, axiom,
% 35.75/36.01    (![A:$i,B:$i]:
% 35.75/36.01     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 35.75/36.01         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 35.75/36.01       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 35.75/36.01  thf('115', plain,
% 35.75/36.01      (![X40 : $i, X41 : $i]:
% 35.75/36.01         (~ (l1_pre_topc @ X40)
% 35.75/36.01          | ~ (v2_pre_topc @ X40)
% 35.75/36.01          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 35.75/36.01          | (v3_pre_topc @ (k1_tops_1 @ X40 @ X41) @ X40))),
% 35.75/36.01      inference('cnf', [status(esa)], [fc9_tops_1])).
% 35.75/36.01  thf('116', plain,
% 35.75/36.01      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 35.75/36.01        | ~ (v2_pre_topc @ sk_A)
% 35.75/36.01        | ~ (l1_pre_topc @ sk_A))),
% 35.75/36.01      inference('sup-', [status(thm)], ['114', '115'])).
% 35.75/36.01  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 35.75/36.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 35.75/36.01  thf('119', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 35.75/36.01      inference('demod', [status(thm)], ['116', '117', '118'])).
% 35.75/36.01  thf('120', plain,
% 35.75/36.01      (((v3_pre_topc @ sk_B_1 @ sk_A))
% 35.75/36.01         <= ((((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01                   (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))))),
% 35.75/36.01      inference('sup+', [status(thm)], ['113', '119'])).
% 35.75/36.01  thf('121', plain,
% 35.75/36.01      ((~ (v3_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((v3_pre_topc @ sk_B_1 @ sk_A)))),
% 35.75/36.01      inference('split', [status(esa)], ['0'])).
% 35.75/36.01  thf('122', plain,
% 35.75/36.01      (~
% 35.75/36.01       (((k2_tops_1 @ sk_A @ sk_B_1)
% 35.75/36.01          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 35.75/36.01             (k2_pre_topc @ sk_A @ sk_B_1) @ sk_B_1))) | 
% 35.75/36.01       ((v3_pre_topc @ sk_B_1 @ sk_A))),
% 35.75/36.01      inference('sup-', [status(thm)], ['120', '121'])).
% 35.75/36.01  thf('123', plain, ($false),
% 35.75/36.01      inference('sat_resolution*', [status(thm)], ['1', '65', '66', '122'])).
% 35.75/36.01  
% 35.75/36.01  % SZS output end Refutation
% 35.75/36.01  
% 35.86/36.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
