%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zU5GzQEj1v

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:29 EST 2020

% Result     : Theorem 34.89s
% Output     : Refutation 34.89s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 229 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :   13
%              Number of atoms          :  768 (2262 expanded)
%              Number of equality atoms :   25 (  64 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t91_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tops_1 @ B @ A )
             => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_tops_1])).

thf('0',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('8',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X48 @ X47 ) @ X47 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X30 @ ( k3_subset_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('14',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k2_pre_topc @ X40 @ ( k3_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 ) ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('28',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('37',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t79_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( v1_tops_1 @ C @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v1_tops_1 @ X49 @ X50 )
      | ~ ( r1_tarski @ X49 @ X51 )
      | ( v1_tops_1 @ X51 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t79_tops_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 )
      | ~ ( v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('42',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tops_1 @ X41 @ X42 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 ) @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('47',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v3_tops_1 @ X43 @ X44 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X44 @ X43 ) @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['45','51'])).

thf('53',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('54',plain,(
    v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','33','34'])).

thf('56',plain,(
    v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','56'])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('61',plain,(
    v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['4','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zU5GzQEj1v
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:27:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 34.89/35.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 34.89/35.08  % Solved by: fo/fo7.sh
% 34.89/35.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 34.89/35.08  % done 68235 iterations in 34.631s
% 34.89/35.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 34.89/35.08  % SZS output start Refutation
% 34.89/35.08  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 34.89/35.08  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 34.89/35.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 34.89/35.08  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 34.89/35.08  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 34.89/35.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 34.89/35.08  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 34.89/35.08  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 34.89/35.08  thf(sk_A_type, type, sk_A: $i).
% 34.89/35.08  thf(sk_B_type, type, sk_B: $i).
% 34.89/35.08  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 34.89/35.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 34.89/35.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 34.89/35.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 34.89/35.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 34.89/35.08  thf(t91_tops_1, conjecture,
% 34.89/35.08    (![A:$i]:
% 34.89/35.08     ( ( l1_pre_topc @ A ) =>
% 34.89/35.08       ( ![B:$i]:
% 34.89/35.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.89/35.08           ( ( v3_tops_1 @ B @ A ) =>
% 34.89/35.08             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 34.89/35.08  thf(zf_stmt_0, negated_conjecture,
% 34.89/35.08    (~( ![A:$i]:
% 34.89/35.08        ( ( l1_pre_topc @ A ) =>
% 34.89/35.08          ( ![B:$i]:
% 34.89/35.08            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.89/35.08              ( ( v3_tops_1 @ B @ A ) =>
% 34.89/35.08                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 34.89/35.08    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 34.89/35.08  thf('0', plain,
% 34.89/35.08      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 34.89/35.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.08  thf('1', plain,
% 34.89/35.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.89/35.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.08  thf(d5_subset_1, axiom,
% 34.89/35.08    (![A:$i,B:$i]:
% 34.89/35.08     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 34.89/35.08       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 34.89/35.08  thf('2', plain,
% 34.89/35.08      (![X27 : $i, X28 : $i]:
% 34.89/35.08         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 34.89/35.08          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 34.89/35.08      inference('cnf', [status(esa)], [d5_subset_1])).
% 34.89/35.08  thf('3', plain,
% 34.89/35.08      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 34.89/35.08         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 34.89/35.08      inference('sup-', [status(thm)], ['1', '2'])).
% 34.89/35.08  thf('4', plain,
% 34.89/35.08      (~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 34.89/35.08      inference('demod', [status(thm)], ['0', '3'])).
% 34.89/35.08  thf(t36_xboole_1, axiom,
% 34.89/35.08    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 34.89/35.08  thf('5', plain,
% 34.89/35.08      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 34.89/35.08      inference('cnf', [status(esa)], [t36_xboole_1])).
% 34.89/35.08  thf(t3_subset, axiom,
% 34.89/35.08    (![A:$i,B:$i]:
% 34.89/35.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 34.89/35.08  thf('6', plain,
% 34.89/35.08      (![X34 : $i, X36 : $i]:
% 34.89/35.08         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 34.89/35.08      inference('cnf', [status(esa)], [t3_subset])).
% 34.89/35.08  thf('7', plain,
% 34.89/35.08      (![X0 : $i, X1 : $i]:
% 34.89/35.08         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 34.89/35.08      inference('sup-', [status(thm)], ['5', '6'])).
% 34.89/35.08  thf(t44_tops_1, axiom,
% 34.89/35.08    (![A:$i]:
% 34.89/35.08     ( ( l1_pre_topc @ A ) =>
% 34.89/35.08       ( ![B:$i]:
% 34.89/35.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.89/35.08           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 34.89/35.08  thf('8', plain,
% 34.89/35.08      (![X47 : $i, X48 : $i]:
% 34.89/35.08         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 34.89/35.08          | (r1_tarski @ (k1_tops_1 @ X48 @ X47) @ X47)
% 34.89/35.08          | ~ (l1_pre_topc @ X48))),
% 34.89/35.08      inference('cnf', [status(esa)], [t44_tops_1])).
% 34.89/35.08  thf('9', plain,
% 34.89/35.08      (![X0 : $i, X1 : $i]:
% 34.89/35.08         (~ (l1_pre_topc @ X0)
% 34.89/35.08          | (r1_tarski @ 
% 34.89/35.08             (k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 34.89/35.08             (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))),
% 34.89/35.08      inference('sup-', [status(thm)], ['7', '8'])).
% 34.89/35.08  thf('10', plain,
% 34.89/35.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.89/35.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.08  thf(involutiveness_k3_subset_1, axiom,
% 34.89/35.08    (![A:$i,B:$i]:
% 34.89/35.08     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 34.89/35.08       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 34.89/35.08  thf('11', plain,
% 34.89/35.08      (![X29 : $i, X30 : $i]:
% 34.89/35.08         (((k3_subset_1 @ X30 @ (k3_subset_1 @ X30 @ X29)) = (X29))
% 34.89/35.08          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 34.89/35.08      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 34.89/35.08  thf('12', plain,
% 34.89/35.08      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 34.89/35.08         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 34.89/35.08      inference('sup-', [status(thm)], ['10', '11'])).
% 34.89/35.08  thf('13', plain,
% 34.89/35.08      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 34.89/35.08         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 34.89/35.08      inference('sup-', [status(thm)], ['1', '2'])).
% 34.89/35.08  thf('14', plain,
% 34.89/35.08      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 34.89/35.08         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 34.89/35.08      inference('demod', [status(thm)], ['12', '13'])).
% 34.89/35.08  thf('15', plain,
% 34.89/35.08      (![X0 : $i, X1 : $i]:
% 34.89/35.08         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 34.89/35.08      inference('sup-', [status(thm)], ['5', '6'])).
% 34.89/35.08  thf('16', plain,
% 34.89/35.08      (![X27 : $i, X28 : $i]:
% 34.89/35.08         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 34.89/35.08          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 34.89/35.08      inference('cnf', [status(esa)], [d5_subset_1])).
% 34.89/35.08  thf('17', plain,
% 34.89/35.08      (![X0 : $i, X1 : $i]:
% 34.89/35.08         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 34.89/35.08           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 34.89/35.08      inference('sup-', [status(thm)], ['15', '16'])).
% 34.89/35.08  thf(t48_xboole_1, axiom,
% 34.89/35.08    (![A:$i,B:$i]:
% 34.89/35.08     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 34.89/35.08  thf('18', plain,
% 34.89/35.08      (![X20 : $i, X21 : $i]:
% 34.89/35.08         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 34.89/35.08           = (k3_xboole_0 @ X20 @ X21))),
% 34.89/35.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 34.89/35.08  thf('19', plain,
% 34.89/35.08      (![X0 : $i, X1 : $i]:
% 34.89/35.08         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 34.89/35.08           = (k3_xboole_0 @ X0 @ X1))),
% 34.89/35.08      inference('demod', [status(thm)], ['17', '18'])).
% 34.89/35.08  thf('20', plain, (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (sk_B))),
% 34.89/35.08      inference('demod', [status(thm)], ['14', '19'])).
% 34.89/35.08  thf('21', plain,
% 34.89/35.08      (![X0 : $i, X1 : $i]:
% 34.89/35.08         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 34.89/35.08      inference('sup-', [status(thm)], ['5', '6'])).
% 34.89/35.08  thf(d1_tops_1, axiom,
% 34.89/35.08    (![A:$i]:
% 34.89/35.08     ( ( l1_pre_topc @ A ) =>
% 34.89/35.08       ( ![B:$i]:
% 34.89/35.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.89/35.08           ( ( k1_tops_1 @ A @ B ) =
% 34.89/35.08             ( k3_subset_1 @
% 34.89/35.08               ( u1_struct_0 @ A ) @ 
% 34.89/35.08               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 34.89/35.08  thf('22', plain,
% 34.89/35.08      (![X39 : $i, X40 : $i]:
% 34.89/35.08         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 34.89/35.08          | ((k1_tops_1 @ X40 @ X39)
% 34.89/35.08              = (k3_subset_1 @ (u1_struct_0 @ X40) @ 
% 34.89/35.08                 (k2_pre_topc @ X40 @ (k3_subset_1 @ (u1_struct_0 @ X40) @ X39))))
% 34.89/35.08          | ~ (l1_pre_topc @ X40))),
% 34.89/35.08      inference('cnf', [status(esa)], [d1_tops_1])).
% 34.89/35.08  thf('23', plain,
% 34.89/35.08      (![X0 : $i, X1 : $i]:
% 34.89/35.08         (~ (l1_pre_topc @ X0)
% 34.89/35.08          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 34.89/35.08              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 34.89/35.08                 (k2_pre_topc @ X0 @ 
% 34.89/35.08                  (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 34.89/35.08                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 34.89/35.08      inference('sup-', [status(thm)], ['21', '22'])).
% 34.89/35.08  thf('24', plain,
% 34.89/35.08      (![X0 : $i, X1 : $i]:
% 34.89/35.08         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 34.89/35.08           = (k3_xboole_0 @ X0 @ X1))),
% 34.89/35.08      inference('demod', [status(thm)], ['17', '18'])).
% 34.89/35.08  thf('25', plain,
% 34.89/35.08      (![X0 : $i, X1 : $i]:
% 34.89/35.08         (~ (l1_pre_topc @ X0)
% 34.89/35.08          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 34.89/35.08              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 34.89/35.08                 (k2_pre_topc @ X0 @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 34.89/35.08      inference('demod', [status(thm)], ['23', '24'])).
% 34.89/35.08  thf('26', plain,
% 34.89/35.09      ((((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 34.89/35.09          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))
% 34.89/35.09        | ~ (l1_pre_topc @ sk_A))),
% 34.89/35.09      inference('sup+', [status(thm)], ['20', '25'])).
% 34.89/35.09  thf('27', plain,
% 34.89/35.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.89/35.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.09  thf(dt_k2_pre_topc, axiom,
% 34.89/35.09    (![A:$i,B:$i]:
% 34.89/35.09     ( ( ( l1_pre_topc @ A ) & 
% 34.89/35.09         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 34.89/35.09       ( m1_subset_1 @
% 34.89/35.09         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 34.89/35.09  thf('28', plain,
% 34.89/35.09      (![X37 : $i, X38 : $i]:
% 34.89/35.09         (~ (l1_pre_topc @ X37)
% 34.89/35.09          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 34.89/35.09          | (m1_subset_1 @ (k2_pre_topc @ X37 @ X38) @ 
% 34.89/35.09             (k1_zfmisc_1 @ (u1_struct_0 @ X37))))),
% 34.89/35.09      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 34.89/35.09  thf('29', plain,
% 34.89/35.09      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 34.89/35.09         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 34.89/35.09        | ~ (l1_pre_topc @ sk_A))),
% 34.89/35.09      inference('sup-', [status(thm)], ['27', '28'])).
% 34.89/35.09  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 34.89/35.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.09  thf('31', plain,
% 34.89/35.09      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 34.89/35.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.89/35.09      inference('demod', [status(thm)], ['29', '30'])).
% 34.89/35.09  thf('32', plain,
% 34.89/35.09      (![X27 : $i, X28 : $i]:
% 34.89/35.09         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 34.89/35.09          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 34.89/35.09      inference('cnf', [status(esa)], [d5_subset_1])).
% 34.89/35.09  thf('33', plain,
% 34.89/35.09      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 34.89/35.09         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 34.89/35.09      inference('sup-', [status(thm)], ['31', '32'])).
% 34.89/35.09  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 34.89/35.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.09  thf('35', plain,
% 34.89/35.09      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 34.89/35.09         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 34.89/35.09      inference('demod', [status(thm)], ['26', '33', '34'])).
% 34.89/35.09  thf('36', plain,
% 34.89/35.09      (![X0 : $i, X1 : $i]:
% 34.89/35.09         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 34.89/35.09      inference('sup-', [status(thm)], ['5', '6'])).
% 34.89/35.09  thf('37', plain,
% 34.89/35.09      ((m1_subset_1 @ 
% 34.89/35.09        (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 34.89/35.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.89/35.09      inference('sup+', [status(thm)], ['35', '36'])).
% 34.89/35.09  thf(t79_tops_1, axiom,
% 34.89/35.09    (![A:$i]:
% 34.89/35.09     ( ( l1_pre_topc @ A ) =>
% 34.89/35.09       ( ![B:$i]:
% 34.89/35.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.89/35.09           ( ![C:$i]:
% 34.89/35.09             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.89/35.09               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 34.89/35.09                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 34.89/35.09  thf('38', plain,
% 34.89/35.09      (![X49 : $i, X50 : $i, X51 : $i]:
% 34.89/35.09         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 34.89/35.09          | ~ (v1_tops_1 @ X49 @ X50)
% 34.89/35.09          | ~ (r1_tarski @ X49 @ X51)
% 34.89/35.09          | (v1_tops_1 @ X51 @ X50)
% 34.89/35.09          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 34.89/35.09          | ~ (l1_pre_topc @ X50))),
% 34.89/35.09      inference('cnf', [status(esa)], [t79_tops_1])).
% 34.89/35.09  thf('39', plain,
% 34.89/35.09      (![X0 : $i]:
% 34.89/35.09         (~ (l1_pre_topc @ sk_A)
% 34.89/35.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 34.89/35.09          | (v1_tops_1 @ X0 @ sk_A)
% 34.89/35.09          | ~ (r1_tarski @ 
% 34.89/35.09               (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 34.89/35.09               X0)
% 34.89/35.09          | ~ (v1_tops_1 @ 
% 34.89/35.09               (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 34.89/35.09               sk_A))),
% 34.89/35.09      inference('sup-', [status(thm)], ['37', '38'])).
% 34.89/35.09  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 34.89/35.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.09  thf('41', plain,
% 34.89/35.09      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 34.89/35.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.89/35.09      inference('demod', [status(thm)], ['29', '30'])).
% 34.89/35.09  thf(d4_tops_1, axiom,
% 34.89/35.09    (![A:$i]:
% 34.89/35.09     ( ( l1_pre_topc @ A ) =>
% 34.89/35.09       ( ![B:$i]:
% 34.89/35.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.89/35.09           ( ( v2_tops_1 @ B @ A ) <=>
% 34.89/35.09             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 34.89/35.09  thf('42', plain,
% 34.89/35.09      (![X41 : $i, X42 : $i]:
% 34.89/35.09         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 34.89/35.09          | ~ (v2_tops_1 @ X41 @ X42)
% 34.89/35.09          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X42) @ X41) @ X42)
% 34.89/35.09          | ~ (l1_pre_topc @ X42))),
% 34.89/35.09      inference('cnf', [status(esa)], [d4_tops_1])).
% 34.89/35.09  thf('43', plain,
% 34.89/35.09      ((~ (l1_pre_topc @ sk_A)
% 34.89/35.09        | (v1_tops_1 @ 
% 34.89/35.09           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 34.89/35.09           sk_A)
% 34.89/35.09        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 34.89/35.09      inference('sup-', [status(thm)], ['41', '42'])).
% 34.89/35.09  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 34.89/35.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.09  thf('45', plain,
% 34.89/35.09      (((v1_tops_1 @ 
% 34.89/35.09         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 34.89/35.09         sk_A)
% 34.89/35.09        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 34.89/35.09      inference('demod', [status(thm)], ['43', '44'])).
% 34.89/35.09  thf('46', plain,
% 34.89/35.09      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.89/35.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.09  thf(d5_tops_1, axiom,
% 34.89/35.09    (![A:$i]:
% 34.89/35.09     ( ( l1_pre_topc @ A ) =>
% 34.89/35.09       ( ![B:$i]:
% 34.89/35.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.89/35.09           ( ( v3_tops_1 @ B @ A ) <=>
% 34.89/35.09             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 34.89/35.09  thf('47', plain,
% 34.89/35.09      (![X43 : $i, X44 : $i]:
% 34.89/35.09         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 34.89/35.09          | ~ (v3_tops_1 @ X43 @ X44)
% 34.89/35.09          | (v2_tops_1 @ (k2_pre_topc @ X44 @ X43) @ X44)
% 34.89/35.09          | ~ (l1_pre_topc @ X44))),
% 34.89/35.09      inference('cnf', [status(esa)], [d5_tops_1])).
% 34.89/35.09  thf('48', plain,
% 34.89/35.09      ((~ (l1_pre_topc @ sk_A)
% 34.89/35.09        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 34.89/35.09        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 34.89/35.09      inference('sup-', [status(thm)], ['46', '47'])).
% 34.89/35.09  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 34.89/35.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.09  thf('50', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 34.89/35.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.09  thf('51', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 34.89/35.09      inference('demod', [status(thm)], ['48', '49', '50'])).
% 34.89/35.09  thf('52', plain,
% 34.89/35.09      ((v1_tops_1 @ 
% 34.89/35.09        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 34.89/35.09        sk_A)),
% 34.89/35.09      inference('demod', [status(thm)], ['45', '51'])).
% 34.89/35.09  thf('53', plain,
% 34.89/35.09      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 34.89/35.09         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 34.89/35.09      inference('sup-', [status(thm)], ['31', '32'])).
% 34.89/35.09  thf('54', plain,
% 34.89/35.09      ((v1_tops_1 @ 
% 34.89/35.09        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 34.89/35.09        sk_A)),
% 34.89/35.09      inference('demod', [status(thm)], ['52', '53'])).
% 34.89/35.09  thf('55', plain,
% 34.89/35.09      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 34.89/35.09         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 34.89/35.09      inference('demod', [status(thm)], ['26', '33', '34'])).
% 34.89/35.09  thf('56', plain,
% 34.89/35.09      ((v1_tops_1 @ 
% 34.89/35.09        (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ sk_A)),
% 34.89/35.09      inference('demod', [status(thm)], ['54', '55'])).
% 34.89/35.09  thf('57', plain,
% 34.89/35.09      (![X0 : $i]:
% 34.89/35.09         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 34.89/35.09          | (v1_tops_1 @ X0 @ sk_A)
% 34.89/35.09          | ~ (r1_tarski @ 
% 34.89/35.09               (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 34.89/35.09               X0))),
% 34.89/35.09      inference('demod', [status(thm)], ['39', '40', '56'])).
% 34.89/35.09  thf('58', plain,
% 34.89/35.09      ((~ (l1_pre_topc @ sk_A)
% 34.89/35.09        | (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 34.89/35.09        | ~ (m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 34.89/35.09             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 34.89/35.09      inference('sup-', [status(thm)], ['9', '57'])).
% 34.89/35.09  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 34.89/35.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.89/35.09  thf('60', plain,
% 34.89/35.09      (![X0 : $i, X1 : $i]:
% 34.89/35.09         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 34.89/35.09      inference('sup-', [status(thm)], ['5', '6'])).
% 34.89/35.09  thf('61', plain,
% 34.89/35.09      ((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 34.89/35.09      inference('demod', [status(thm)], ['58', '59', '60'])).
% 34.89/35.09  thf('62', plain, ($false), inference('demod', [status(thm)], ['4', '61'])).
% 34.89/35.09  
% 34.89/35.09  % SZS output end Refutation
% 34.89/35.09  
% 34.89/35.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
