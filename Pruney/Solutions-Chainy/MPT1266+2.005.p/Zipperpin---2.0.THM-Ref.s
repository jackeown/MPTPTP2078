%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gfp02gDnH7

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:12 EST 2020

% Result     : Theorem 3.30s
% Output     : Refutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  284 (2119 expanded)
%              Number of leaves         :   39 ( 673 expanded)
%              Depth                    :   29
%              Number of atoms          : 2296 (17343 expanded)
%              Number of equality atoms :  189 (1445 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(t84_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( ( k1_tops_1 @ A @ B )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_tops_1])).

thf('0',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('9',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('28',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tops_1 @ X29 @ X30 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('36',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('38',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','39'])).

thf('41',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','40'])).

thf('42',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['24','41'])).

thf('43',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['17','42'])).

thf('44',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v1_tops_1 @ X27 @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = ( k2_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('61',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('63',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('65',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','63','64'])).

thf('66',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('73',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('74',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('76',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['66','77'])).

thf('79',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_B )
        = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['2','78'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('80',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('81',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('85',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('87',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('88',plain,(
    ! [X17: $i] :
      ( ( k2_subset_1 @ X17 )
      = ( k3_subset_1 @ X17 @ ( k1_subset_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('89',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('90',plain,(
    ! [X17: $i] :
      ( X17
      = ( k3_subset_1 @ X17 @ ( k1_subset_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('94',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','92','93'])).

thf('95',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('99',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('100',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('101',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_pre_topc @ X28 @ X27 )
       != ( k2_struct_0 @ X28 ) )
      | ( v1_tops_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('106',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('107',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('110',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('111',plain,(
    r1_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('114',plain,(
    r1_tarski @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('116',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('118',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('120',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('121',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('122',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['119','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('125',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('127',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['118','125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('129',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('130',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) )
        = ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['127','136'])).

thf('138',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('139',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('140',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('141',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('145',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('147',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('149',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('151',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('153',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('155',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('156',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('168',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['80','83'])).

thf('173',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','90'])).

thf('178',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['171','178'])).

thf('180',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('185',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['183','190'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['166','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['159','192'])).

thf('194',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['154','193'])).

thf('195',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('196',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('199',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('201',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['153','201'])).

thf('203',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('204',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('205',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('207',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('209',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['154','193'])).

thf('210',plain,
    ( ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('212',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('214',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('217',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('219',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['207','219'])).

thf('221',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['202','220'])).

thf('222',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['118','125','126'])).

thf('223',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','138','221','222','223'])).

thf('225',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','224'])).

thf('226',plain,
    ( ( ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['99','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('228',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ( v2_tops_1 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('232',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('235',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['232','233','234'])).

thf('236',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('237',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('239',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['229','239'])).

thf('241',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('242',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','97','98','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gfp02gDnH7
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:24:25 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.30/3.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.30/3.50  % Solved by: fo/fo7.sh
% 3.30/3.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.30/3.50  % done 11081 iterations in 3.055s
% 3.30/3.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.30/3.50  % SZS output start Refutation
% 3.30/3.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.30/3.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.30/3.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.30/3.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.30/3.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.30/3.50  thf(sk_A_type, type, sk_A: $i).
% 3.30/3.50  thf(sk_B_type, type, sk_B: $i).
% 3.30/3.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.30/3.50  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 3.30/3.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.30/3.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.30/3.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 3.30/3.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.30/3.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.30/3.50  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 3.30/3.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 3.30/3.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.30/3.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.30/3.50  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 3.30/3.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.30/3.50  thf(t84_tops_1, conjecture,
% 3.30/3.50    (![A:$i]:
% 3.30/3.50     ( ( l1_pre_topc @ A ) =>
% 3.30/3.50       ( ![B:$i]:
% 3.30/3.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.30/3.50           ( ( v2_tops_1 @ B @ A ) <=>
% 3.30/3.50             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 3.30/3.50  thf(zf_stmt_0, negated_conjecture,
% 3.30/3.50    (~( ![A:$i]:
% 3.30/3.50        ( ( l1_pre_topc @ A ) =>
% 3.30/3.50          ( ![B:$i]:
% 3.30/3.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.30/3.50              ( ( v2_tops_1 @ B @ A ) <=>
% 3.30/3.50                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 3.30/3.50    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 3.30/3.50  thf('0', plain,
% 3.30/3.50      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 3.30/3.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('1', plain,
% 3.30/3.50      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 3.30/3.50       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 3.30/3.50      inference('split', [status(esa)], ['0'])).
% 3.30/3.50  thf(d3_struct_0, axiom,
% 3.30/3.50    (![A:$i]:
% 3.30/3.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 3.30/3.50  thf('2', plain,
% 3.30/3.50      (![X21 : $i]:
% 3.30/3.50         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.30/3.50  thf('3', plain,
% 3.30/3.50      (![X21 : $i]:
% 3.30/3.50         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.30/3.50  thf('4', plain,
% 3.30/3.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf(t3_subset, axiom,
% 3.30/3.50    (![A:$i,B:$i]:
% 3.30/3.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.30/3.50  thf('5', plain,
% 3.30/3.50      (![X18 : $i, X19 : $i]:
% 3.30/3.50         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 3.30/3.50      inference('cnf', [status(esa)], [t3_subset])).
% 3.30/3.50  thf('6', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup-', [status(thm)], ['4', '5'])).
% 3.30/3.50  thf('7', plain,
% 3.30/3.50      (((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup+', [status(thm)], ['3', '6'])).
% 3.30/3.50  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf(dt_l1_pre_topc, axiom,
% 3.30/3.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 3.30/3.50  thf('9', plain, (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 3.30/3.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.30/3.50  thf('10', plain, ((l1_struct_0 @ sk_A)),
% 3.30/3.50      inference('sup-', [status(thm)], ['8', '9'])).
% 3.30/3.50  thf('11', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 3.30/3.50      inference('demod', [status(thm)], ['7', '10'])).
% 3.30/3.50  thf(t28_xboole_1, axiom,
% 3.30/3.50    (![A:$i,B:$i]:
% 3.30/3.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.30/3.50  thf('12', plain,
% 3.30/3.50      (![X4 : $i, X5 : $i]:
% 3.30/3.50         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 3.30/3.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.30/3.50  thf('13', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (sk_B))),
% 3.30/3.50      inference('sup-', [status(thm)], ['11', '12'])).
% 3.30/3.50  thf(commutativity_k3_xboole_0, axiom,
% 3.30/3.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.30/3.50  thf('14', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.30/3.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.30/3.50  thf(t100_xboole_1, axiom,
% 3.30/3.50    (![A:$i,B:$i]:
% 3.30/3.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.30/3.50  thf('15', plain,
% 3.30/3.50      (![X2 : $i, X3 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X2 @ X3)
% 3.30/3.50           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 3.30/3.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.30/3.50  thf('16', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X0 @ X1)
% 3.30/3.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['14', '15'])).
% 3.30/3.50  thf('17', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup+', [status(thm)], ['13', '16'])).
% 3.30/3.50  thf('18', plain,
% 3.30/3.50      (![X21 : $i]:
% 3.30/3.50         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.30/3.50  thf('19', plain,
% 3.30/3.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('20', plain,
% 3.30/3.50      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 3.30/3.50        | ~ (l1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup+', [status(thm)], ['18', '19'])).
% 3.30/3.50  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 3.30/3.50      inference('sup-', [status(thm)], ['8', '9'])).
% 3.30/3.50  thf('22', plain,
% 3.30/3.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 3.30/3.50      inference('demod', [status(thm)], ['20', '21'])).
% 3.30/3.50  thf(d5_subset_1, axiom,
% 3.30/3.50    (![A:$i,B:$i]:
% 3.30/3.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.30/3.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.30/3.50  thf('23', plain,
% 3.30/3.50      (![X13 : $i, X14 : $i]:
% 3.30/3.50         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 3.30/3.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 3.30/3.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.30/3.50  thf('24', plain,
% 3.30/3.50      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup-', [status(thm)], ['22', '23'])).
% 3.30/3.50  thf('25', plain,
% 3.30/3.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('26', plain,
% 3.30/3.50      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 3.30/3.50      inference('split', [status(esa)], ['25'])).
% 3.30/3.50  thf('27', plain,
% 3.30/3.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf(d4_tops_1, axiom,
% 3.30/3.50    (![A:$i]:
% 3.30/3.50     ( ( l1_pre_topc @ A ) =>
% 3.30/3.50       ( ![B:$i]:
% 3.30/3.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.30/3.50           ( ( v2_tops_1 @ B @ A ) <=>
% 3.30/3.50             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 3.30/3.50  thf('28', plain,
% 3.30/3.50      (![X29 : $i, X30 : $i]:
% 3.30/3.50         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 3.30/3.50          | ~ (v2_tops_1 @ X29 @ X30)
% 3.30/3.50          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 3.30/3.50          | ~ (l1_pre_topc @ X30))),
% 3.30/3.50      inference('cnf', [status(esa)], [d4_tops_1])).
% 3.30/3.50  thf('29', plain,
% 3.30/3.50      ((~ (l1_pre_topc @ sk_A)
% 3.30/3.50        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 3.30/3.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 3.30/3.50      inference('sup-', [status(thm)], ['27', '28'])).
% 3.30/3.50  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('31', plain,
% 3.30/3.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('32', plain,
% 3.30/3.50      (![X13 : $i, X14 : $i]:
% 3.30/3.50         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 3.30/3.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 3.30/3.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.30/3.50  thf('33', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup-', [status(thm)], ['31', '32'])).
% 3.30/3.50  thf('34', plain,
% 3.30/3.50      (![X21 : $i]:
% 3.30/3.50         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.30/3.50  thf('35', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup-', [status(thm)], ['31', '32'])).
% 3.30/3.50  thf('36', plain,
% 3.30/3.50      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50        | ~ (l1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup+', [status(thm)], ['34', '35'])).
% 3.30/3.50  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 3.30/3.50      inference('sup-', [status(thm)], ['8', '9'])).
% 3.30/3.50  thf('38', plain,
% 3.30/3.50      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['36', '37'])).
% 3.30/3.50  thf('39', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['33', '38'])).
% 3.30/3.50  thf('40', plain,
% 3.30/3.50      (((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 3.30/3.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 3.30/3.50      inference('demod', [status(thm)], ['29', '30', '39'])).
% 3.30/3.50  thf('41', plain,
% 3.30/3.50      (((v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 3.30/3.50         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 3.30/3.50      inference('sup-', [status(thm)], ['26', '40'])).
% 3.30/3.50  thf('42', plain,
% 3.30/3.50      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 3.30/3.50         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['24', '41'])).
% 3.30/3.50  thf('43', plain,
% 3.30/3.50      (((v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 3.30/3.50         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['17', '42'])).
% 3.30/3.50  thf('44', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup-', [status(thm)], ['4', '5'])).
% 3.30/3.50  thf('45', plain,
% 3.30/3.50      (![X4 : $i, X5 : $i]:
% 3.30/3.50         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 3.30/3.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.30/3.50  thf('46', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 3.30/3.50      inference('sup-', [status(thm)], ['44', '45'])).
% 3.30/3.50  thf('47', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X0 @ X1)
% 3.30/3.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['14', '15'])).
% 3.30/3.50  thf('48', plain,
% 3.30/3.50      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup+', [status(thm)], ['46', '47'])).
% 3.30/3.50  thf(t36_xboole_1, axiom,
% 3.30/3.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.30/3.50  thf('49', plain,
% 3.30/3.50      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 3.30/3.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.30/3.50  thf('50', plain,
% 3.30/3.50      (![X18 : $i, X20 : $i]:
% 3.30/3.50         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 3.30/3.50      inference('cnf', [status(esa)], [t3_subset])).
% 3.30/3.50  thf('51', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.30/3.50      inference('sup-', [status(thm)], ['49', '50'])).
% 3.30/3.50  thf('52', plain,
% 3.30/3.50      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.30/3.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['48', '51'])).
% 3.30/3.50  thf(d3_tops_1, axiom,
% 3.30/3.50    (![A:$i]:
% 3.30/3.50     ( ( l1_pre_topc @ A ) =>
% 3.30/3.50       ( ![B:$i]:
% 3.30/3.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.30/3.50           ( ( v1_tops_1 @ B @ A ) <=>
% 3.30/3.50             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 3.30/3.50  thf('53', plain,
% 3.30/3.50      (![X27 : $i, X28 : $i]:
% 3.30/3.50         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 3.30/3.50          | ~ (v1_tops_1 @ X27 @ X28)
% 3.30/3.50          | ((k2_pre_topc @ X28 @ X27) = (k2_struct_0 @ X28))
% 3.30/3.50          | ~ (l1_pre_topc @ X28))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_tops_1])).
% 3.30/3.50  thf('54', plain,
% 3.30/3.50      ((~ (l1_pre_topc @ sk_A)
% 3.30/3.50        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50            = (k2_struct_0 @ sk_A))
% 3.30/3.50        | ~ (v1_tops_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 3.30/3.50      inference('sup-', [status(thm)], ['52', '53'])).
% 3.30/3.50  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('56', plain,
% 3.30/3.50      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50          = (k2_struct_0 @ sk_A))
% 3.30/3.50        | ~ (v1_tops_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 3.30/3.50      inference('demod', [status(thm)], ['54', '55'])).
% 3.30/3.50  thf('57', plain,
% 3.30/3.50      (![X21 : $i]:
% 3.30/3.50         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.30/3.50  thf('58', plain,
% 3.30/3.50      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup+', [status(thm)], ['46', '47'])).
% 3.30/3.50  thf('59', plain,
% 3.30/3.50      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50        | ~ (l1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup+', [status(thm)], ['57', '58'])).
% 3.30/3.50  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 3.30/3.50      inference('sup-', [status(thm)], ['8', '9'])).
% 3.30/3.50  thf('61', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.50  thf('62', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup+', [status(thm)], ['13', '16'])).
% 3.30/3.50  thf('63', plain,
% 3.30/3.50      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['61', '62'])).
% 3.30/3.50  thf('64', plain,
% 3.30/3.50      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['61', '62'])).
% 3.30/3.50  thf('65', plain,
% 3.30/3.50      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50          = (k2_struct_0 @ sk_A))
% 3.30/3.50        | ~ (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 3.30/3.50      inference('demod', [status(thm)], ['56', '63', '64'])).
% 3.30/3.50  thf('66', plain,
% 3.30/3.50      ((((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50          = (k2_struct_0 @ sk_A)))
% 3.30/3.50         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 3.30/3.50      inference('sup-', [status(thm)], ['43', '65'])).
% 3.30/3.50  thf('67', plain,
% 3.30/3.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf(d1_tops_1, axiom,
% 3.30/3.50    (![A:$i]:
% 3.30/3.50     ( ( l1_pre_topc @ A ) =>
% 3.30/3.50       ( ![B:$i]:
% 3.30/3.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.30/3.50           ( ( k1_tops_1 @ A @ B ) =
% 3.30/3.50             ( k3_subset_1 @
% 3.30/3.50               ( u1_struct_0 @ A ) @ 
% 3.30/3.50               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 3.30/3.50  thf('68', plain,
% 3.30/3.50      (![X25 : $i, X26 : $i]:
% 3.30/3.50         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 3.30/3.50          | ((k1_tops_1 @ X26 @ X25)
% 3.30/3.50              = (k3_subset_1 @ (u1_struct_0 @ X26) @ 
% 3.30/3.50                 (k2_pre_topc @ X26 @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25))))
% 3.30/3.50          | ~ (l1_pre_topc @ X26))),
% 3.30/3.50      inference('cnf', [status(esa)], [d1_tops_1])).
% 3.30/3.50  thf('69', plain,
% 3.30/3.50      ((~ (l1_pre_topc @ sk_A)
% 3.30/3.50        | ((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50               (k2_pre_topc @ sk_A @ 
% 3.30/3.50                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 3.30/3.50      inference('sup-', [status(thm)], ['67', '68'])).
% 3.30/3.50  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('71', plain,
% 3.30/3.50      (((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 3.30/3.50      inference('demod', [status(thm)], ['69', '70'])).
% 3.30/3.50  thf('72', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['33', '38'])).
% 3.30/3.50  thf('73', plain,
% 3.30/3.50      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup-', [status(thm)], ['22', '23'])).
% 3.30/3.50  thf('74', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['72', '73'])).
% 3.30/3.50  thf('75', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup+', [status(thm)], ['13', '16'])).
% 3.30/3.50  thf('76', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['74', '75'])).
% 3.30/3.50  thf('77', plain,
% 3.30/3.50      (((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 3.30/3.50      inference('demod', [status(thm)], ['71', '76'])).
% 3.30/3.50  thf('78', plain,
% 3.30/3.50      ((((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 3.30/3.50         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['66', '77'])).
% 3.30/3.50  thf('79', plain,
% 3.30/3.50      (((((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50           = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 3.30/3.50         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['2', '78'])).
% 3.30/3.50  thf(t2_boole, axiom,
% 3.30/3.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.30/3.50  thf('80', plain,
% 3.30/3.50      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.30/3.50      inference('cnf', [status(esa)], [t2_boole])).
% 3.30/3.50  thf(t48_xboole_1, axiom,
% 3.30/3.50    (![A:$i,B:$i]:
% 3.30/3.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.30/3.50  thf('81', plain,
% 3.30/3.50      (![X9 : $i, X10 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 3.30/3.50           = (k3_xboole_0 @ X9 @ X10))),
% 3.30/3.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.30/3.50  thf('82', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.30/3.50      inference('sup-', [status(thm)], ['49', '50'])).
% 3.30/3.50  thf('83', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 3.30/3.50      inference('sup+', [status(thm)], ['81', '82'])).
% 3.30/3.50  thf('84', plain,
% 3.30/3.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['80', '83'])).
% 3.30/3.50  thf(involutiveness_k3_subset_1, axiom,
% 3.30/3.50    (![A:$i,B:$i]:
% 3.30/3.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.30/3.50       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 3.30/3.50  thf('85', plain,
% 3.30/3.50      (![X15 : $i, X16 : $i]:
% 3.30/3.50         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 3.30/3.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 3.30/3.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.30/3.50  thf('86', plain,
% 3.30/3.50      (![X0 : $i]:
% 3.30/3.50         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 3.30/3.50      inference('sup-', [status(thm)], ['84', '85'])).
% 3.30/3.50  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 3.30/3.50  thf('87', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 3.30/3.50  thf(t22_subset_1, axiom,
% 3.30/3.50    (![A:$i]:
% 3.30/3.50     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 3.30/3.50  thf('88', plain,
% 3.30/3.50      (![X17 : $i]:
% 3.30/3.50         ((k2_subset_1 @ X17) = (k3_subset_1 @ X17 @ (k1_subset_1 @ X17)))),
% 3.30/3.50      inference('cnf', [status(esa)], [t22_subset_1])).
% 3.30/3.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.30/3.50  thf('89', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 3.30/3.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.30/3.50  thf('90', plain,
% 3.30/3.50      (![X17 : $i]: ((X17) = (k3_subset_1 @ X17 @ (k1_subset_1 @ X17)))),
% 3.30/3.50      inference('demod', [status(thm)], ['88', '89'])).
% 3.30/3.50  thf('91', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['87', '90'])).
% 3.30/3.50  thf('92', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 3.30/3.50      inference('demod', [status(thm)], ['86', '91'])).
% 3.30/3.50  thf('93', plain, ((l1_struct_0 @ sk_A)),
% 3.30/3.50      inference('sup-', [status(thm)], ['8', '9'])).
% 3.30/3.50  thf('94', plain,
% 3.30/3.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 3.30/3.50         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 3.30/3.50      inference('demod', [status(thm)], ['79', '92', '93'])).
% 3.30/3.50  thf('95', plain,
% 3.30/3.50      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 3.30/3.50         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.30/3.50      inference('split', [status(esa)], ['0'])).
% 3.30/3.50  thf('96', plain,
% 3.30/3.50      ((((k1_xboole_0) != (k1_xboole_0)))
% 3.30/3.50         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 3.30/3.50             ((v2_tops_1 @ sk_B @ sk_A)))),
% 3.30/3.50      inference('sup-', [status(thm)], ['94', '95'])).
% 3.30/3.50  thf('97', plain,
% 3.30/3.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 3.30/3.50       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 3.30/3.50      inference('simplify', [status(thm)], ['96'])).
% 3.30/3.50  thf('98', plain,
% 3.30/3.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 3.30/3.50       ((v2_tops_1 @ sk_B @ sk_A))),
% 3.30/3.50      inference('split', [status(esa)], ['25'])).
% 3.30/3.50  thf('99', plain,
% 3.30/3.50      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 3.30/3.50         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.30/3.50      inference('split', [status(esa)], ['25'])).
% 3.30/3.50  thf('100', plain,
% 3.30/3.50      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.30/3.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['48', '51'])).
% 3.30/3.50  thf('101', plain,
% 3.30/3.50      (![X27 : $i, X28 : $i]:
% 3.30/3.50         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 3.30/3.50          | ((k2_pre_topc @ X28 @ X27) != (k2_struct_0 @ X28))
% 3.30/3.50          | (v1_tops_1 @ X27 @ X28)
% 3.30/3.50          | ~ (l1_pre_topc @ X28))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_tops_1])).
% 3.30/3.50  thf('102', plain,
% 3.30/3.50      ((~ (l1_pre_topc @ sk_A)
% 3.30/3.50        | (v1_tops_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 3.30/3.50        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50            != (k2_struct_0 @ sk_A)))),
% 3.30/3.50      inference('sup-', [status(thm)], ['100', '101'])).
% 3.30/3.50  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('104', plain,
% 3.30/3.50      (((v1_tops_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 3.30/3.50        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50            != (k2_struct_0 @ sk_A)))),
% 3.30/3.50      inference('demod', [status(thm)], ['102', '103'])).
% 3.30/3.50  thf('105', plain,
% 3.30/3.50      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['61', '62'])).
% 3.30/3.50  thf('106', plain,
% 3.30/3.50      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['61', '62'])).
% 3.30/3.50  thf('107', plain,
% 3.30/3.50      (((v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 3.30/3.50        | ((k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50            != (k2_struct_0 @ sk_A)))),
% 3.30/3.50      inference('demod', [status(thm)], ['104', '105', '106'])).
% 3.30/3.50  thf('108', plain,
% 3.30/3.50      (![X21 : $i]:
% 3.30/3.50         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.30/3.50  thf('109', plain,
% 3.30/3.50      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['36', '37'])).
% 3.30/3.50  thf('110', plain,
% 3.30/3.50      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 3.30/3.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.30/3.50  thf('111', plain,
% 3.30/3.50      ((r1_tarski @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 3.30/3.50        (u1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup+', [status(thm)], ['109', '110'])).
% 3.30/3.50  thf('112', plain,
% 3.30/3.50      (((r1_tarski @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 3.30/3.50         (k2_struct_0 @ sk_A))
% 3.30/3.50        | ~ (l1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup+', [status(thm)], ['108', '111'])).
% 3.30/3.50  thf('113', plain, ((l1_struct_0 @ sk_A)),
% 3.30/3.50      inference('sup-', [status(thm)], ['8', '9'])).
% 3.30/3.50  thf('114', plain,
% 3.30/3.50      ((r1_tarski @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 3.30/3.50        (k2_struct_0 @ sk_A))),
% 3.30/3.50      inference('demod', [status(thm)], ['112', '113'])).
% 3.30/3.50  thf('115', plain,
% 3.30/3.50      (![X4 : $i, X5 : $i]:
% 3.30/3.50         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 3.30/3.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.30/3.50  thf('116', plain,
% 3.30/3.50      (((k3_xboole_0 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 3.30/3.50         (k2_struct_0 @ sk_A)) = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup-', [status(thm)], ['114', '115'])).
% 3.30/3.50  thf('117', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.30/3.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.30/3.50  thf('118', plain,
% 3.30/3.50      (((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 3.30/3.50         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['116', '117'])).
% 3.30/3.50  thf('119', plain,
% 3.30/3.50      (![X21 : $i]:
% 3.30/3.50         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.30/3.50  thf('120', plain,
% 3.30/3.50      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup+', [status(thm)], ['46', '47'])).
% 3.30/3.50  thf('121', plain,
% 3.30/3.50      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['36', '37'])).
% 3.30/3.50  thf('122', plain,
% 3.30/3.50      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup+', [status(thm)], ['120', '121'])).
% 3.30/3.50  thf('123', plain,
% 3.30/3.50      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50          = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50        | ~ (l1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup+', [status(thm)], ['119', '122'])).
% 3.30/3.50  thf('124', plain, ((l1_struct_0 @ sk_A)),
% 3.30/3.50      inference('sup-', [status(thm)], ['8', '9'])).
% 3.30/3.50  thf('125', plain,
% 3.30/3.50      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['123', '124'])).
% 3.30/3.50  thf('126', plain,
% 3.30/3.50      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['123', '124'])).
% 3.30/3.50  thf('127', plain,
% 3.30/3.50      (((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 3.30/3.50         (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['118', '125', '126'])).
% 3.30/3.50  thf('128', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 3.30/3.50      inference('sup+', [status(thm)], ['81', '82'])).
% 3.30/3.50  thf('129', plain,
% 3.30/3.50      (![X21 : $i]:
% 3.30/3.50         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.30/3.50  thf(dt_k2_pre_topc, axiom,
% 3.30/3.50    (![A:$i,B:$i]:
% 3.30/3.50     ( ( ( l1_pre_topc @ A ) & 
% 3.30/3.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.30/3.50       ( m1_subset_1 @
% 3.30/3.50         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.30/3.50  thf('130', plain,
% 3.30/3.50      (![X22 : $i, X23 : $i]:
% 3.30/3.50         (~ (l1_pre_topc @ X22)
% 3.30/3.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 3.30/3.50          | (m1_subset_1 @ (k2_pre_topc @ X22 @ X23) @ 
% 3.30/3.50             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 3.30/3.50      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 3.30/3.50  thf('131', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 3.30/3.50          | ~ (l1_struct_0 @ X0)
% 3.30/3.50          | (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 3.30/3.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.30/3.50          | ~ (l1_pre_topc @ X0))),
% 3.30/3.50      inference('sup-', [status(thm)], ['129', '130'])).
% 3.30/3.50  thf('132', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         (~ (l1_pre_topc @ X0)
% 3.30/3.50          | (m1_subset_1 @ 
% 3.30/3.50             (k2_pre_topc @ X0 @ (k3_xboole_0 @ (k2_struct_0 @ X0) @ X1)) @ 
% 3.30/3.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.30/3.50          | ~ (l1_struct_0 @ X0))),
% 3.30/3.50      inference('sup-', [status(thm)], ['128', '131'])).
% 3.30/3.50  thf('133', plain,
% 3.30/3.50      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 3.30/3.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 3.30/3.50  thf('134', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((m1_subset_1 @ 
% 3.30/3.50           (k2_pre_topc @ X0 @ (k3_xboole_0 @ (k2_struct_0 @ X0) @ X1)) @ 
% 3.30/3.50           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 3.30/3.50          | ~ (l1_pre_topc @ X0))),
% 3.30/3.50      inference('clc', [status(thm)], ['132', '133'])).
% 3.30/3.50  thf('135', plain,
% 3.30/3.50      (![X15 : $i, X16 : $i]:
% 3.30/3.50         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 3.30/3.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 3.30/3.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.30/3.50  thf('136', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         (~ (l1_pre_topc @ X0)
% 3.30/3.50          | ((k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 3.30/3.50              (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 3.30/3.50               (k2_pre_topc @ X0 @ (k3_xboole_0 @ (k2_struct_0 @ X0) @ X1))))
% 3.30/3.50              = (k2_pre_topc @ X0 @ (k3_xboole_0 @ (k2_struct_0 @ X0) @ X1))))),
% 3.30/3.50      inference('sup-', [status(thm)], ['134', '135'])).
% 3.30/3.50  thf('137', plain,
% 3.30/3.50      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50           (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 3.30/3.50          = (k2_pre_topc @ sk_A @ 
% 3.30/3.50             (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 3.30/3.50              (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 3.30/3.50        | ~ (l1_pre_topc @ sk_A))),
% 3.30/3.50      inference('sup+', [status(thm)], ['127', '136'])).
% 3.30/3.50  thf('138', plain,
% 3.30/3.50      (((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 3.30/3.50      inference('demod', [status(thm)], ['71', '76'])).
% 3.30/3.50  thf('139', plain,
% 3.30/3.50      ((m1_subset_1 @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 3.30/3.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['48', '51'])).
% 3.30/3.50  thf('140', plain,
% 3.30/3.50      (![X22 : $i, X23 : $i]:
% 3.30/3.50         (~ (l1_pre_topc @ X22)
% 3.30/3.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 3.30/3.50          | (m1_subset_1 @ (k2_pre_topc @ X22 @ X23) @ 
% 3.30/3.50             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 3.30/3.50      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 3.30/3.50  thf('141', plain,
% 3.30/3.50      (((m1_subset_1 @ 
% 3.30/3.50         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 3.30/3.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.30/3.50        | ~ (l1_pre_topc @ sk_A))),
% 3.30/3.50      inference('sup-', [status(thm)], ['139', '140'])).
% 3.30/3.50  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('143', plain,
% 3.30/3.50      ((m1_subset_1 @ 
% 3.30/3.50        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 3.30/3.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('demod', [status(thm)], ['141', '142'])).
% 3.30/3.50  thf('144', plain,
% 3.30/3.50      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['61', '62'])).
% 3.30/3.50  thf('145', plain,
% 3.30/3.50      ((m1_subset_1 @ 
% 3.30/3.50        (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 3.30/3.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('demod', [status(thm)], ['143', '144'])).
% 3.30/3.50  thf('146', plain,
% 3.30/3.50      (![X13 : $i, X14 : $i]:
% 3.30/3.50         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 3.30/3.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 3.30/3.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.30/3.50  thf('147', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50         (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 3.30/3.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 3.30/3.50      inference('sup-', [status(thm)], ['145', '146'])).
% 3.30/3.50  thf('148', plain,
% 3.30/3.50      (((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 3.30/3.50      inference('demod', [status(thm)], ['71', '76'])).
% 3.30/3.50  thf('149', plain,
% 3.30/3.50      (((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 3.30/3.50      inference('sup+', [status(thm)], ['147', '148'])).
% 3.30/3.50  thf('150', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.30/3.50      inference('sup-', [status(thm)], ['49', '50'])).
% 3.30/3.50  thf('151', plain,
% 3.30/3.50      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.30/3.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['149', '150'])).
% 3.30/3.50  thf('152', plain,
% 3.30/3.50      (![X13 : $i, X14 : $i]:
% 3.30/3.50         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 3.30/3.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 3.30/3.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.30/3.50  thf('153', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.30/3.50      inference('sup-', [status(thm)], ['151', '152'])).
% 3.30/3.50  thf('154', plain,
% 3.30/3.50      (((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.30/3.50            (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 3.30/3.50      inference('sup+', [status(thm)], ['147', '148'])).
% 3.30/3.50  thf('155', plain,
% 3.30/3.50      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 3.30/3.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.30/3.50  thf('156', plain,
% 3.30/3.50      (![X4 : $i, X5 : $i]:
% 3.30/3.50         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 3.30/3.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.30/3.50  thf('157', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 3.30/3.50           = (k4_xboole_0 @ X0 @ X1))),
% 3.30/3.50      inference('sup-', [status(thm)], ['155', '156'])).
% 3.30/3.50  thf('158', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.30/3.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.30/3.50  thf('159', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.30/3.50           = (k4_xboole_0 @ X0 @ X1))),
% 3.30/3.50      inference('demod', [status(thm)], ['157', '158'])).
% 3.30/3.50  thf('160', plain,
% 3.30/3.50      (![X9 : $i, X10 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 3.30/3.50           = (k3_xboole_0 @ X9 @ X10))),
% 3.30/3.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.30/3.50  thf('161', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.30/3.50           = (k4_xboole_0 @ X0 @ X1))),
% 3.30/3.50      inference('demod', [status(thm)], ['157', '158'])).
% 3.30/3.50  thf('162', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.30/3.50           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['160', '161'])).
% 3.30/3.50  thf('163', plain,
% 3.30/3.50      (![X9 : $i, X10 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 3.30/3.50           = (k3_xboole_0 @ X9 @ X10))),
% 3.30/3.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.30/3.50  thf('164', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.30/3.50           = (k3_xboole_0 @ X1 @ X0))),
% 3.30/3.50      inference('demod', [status(thm)], ['162', '163'])).
% 3.30/3.50  thf('165', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X0 @ X1)
% 3.30/3.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['14', '15'])).
% 3.30/3.50  thf('166', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 3.30/3.50           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['164', '165'])).
% 3.30/3.50  thf('167', plain,
% 3.30/3.50      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.30/3.50      inference('cnf', [status(esa)], [t2_boole])).
% 3.30/3.50  thf('168', plain,
% 3.30/3.50      (![X2 : $i, X3 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X2 @ X3)
% 3.30/3.50           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 3.30/3.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.30/3.50  thf('169', plain,
% 3.30/3.50      (![X0 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['167', '168'])).
% 3.30/3.50  thf('170', plain,
% 3.30/3.50      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 3.30/3.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.30/3.50  thf('171', plain,
% 3.30/3.50      (![X0 : $i]: (r1_tarski @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 3.30/3.50      inference('sup+', [status(thm)], ['169', '170'])).
% 3.30/3.50  thf('172', plain,
% 3.30/3.50      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['80', '83'])).
% 3.30/3.50  thf('173', plain,
% 3.30/3.50      (![X13 : $i, X14 : $i]:
% 3.30/3.50         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 3.30/3.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 3.30/3.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.30/3.50  thf('174', plain,
% 3.30/3.50      (![X0 : $i]:
% 3.30/3.50         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('sup-', [status(thm)], ['172', '173'])).
% 3.30/3.50  thf('175', plain,
% 3.30/3.50      (![X0 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['167', '168'])).
% 3.30/3.50  thf('176', plain,
% 3.30/3.50      (![X0 : $i]:
% 3.30/3.50         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('demod', [status(thm)], ['174', '175'])).
% 3.30/3.50  thf('177', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['87', '90'])).
% 3.30/3.50  thf('178', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['176', '177'])).
% 3.30/3.50  thf('179', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.30/3.50      inference('demod', [status(thm)], ['171', '178'])).
% 3.30/3.50  thf('180', plain,
% 3.30/3.50      (![X4 : $i, X5 : $i]:
% 3.30/3.50         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 3.30/3.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.30/3.50  thf('181', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.30/3.50      inference('sup-', [status(thm)], ['179', '180'])).
% 3.30/3.50  thf('182', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X0 @ X1)
% 3.30/3.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['14', '15'])).
% 3.30/3.50  thf('183', plain,
% 3.30/3.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['181', '182'])).
% 3.30/3.50  thf('184', plain,
% 3.30/3.50      (![X0 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['167', '168'])).
% 3.30/3.50  thf('185', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['176', '177'])).
% 3.30/3.50  thf('186', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.30/3.50      inference('demod', [status(thm)], ['184', '185'])).
% 3.30/3.50  thf('187', plain,
% 3.30/3.50      (![X9 : $i, X10 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 3.30/3.50           = (k3_xboole_0 @ X9 @ X10))),
% 3.30/3.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.30/3.50  thf('188', plain,
% 3.30/3.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['186', '187'])).
% 3.30/3.50  thf('189', plain,
% 3.30/3.50      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 3.30/3.50      inference('cnf', [status(esa)], [t2_boole])).
% 3.30/3.50  thf('190', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.30/3.50      inference('demod', [status(thm)], ['188', '189'])).
% 3.30/3.50  thf('191', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['183', '190'])).
% 3.30/3.50  thf('192', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 3.30/3.50      inference('demod', [status(thm)], ['166', '191'])).
% 3.30/3.50  thf('193', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['159', '192'])).
% 3.30/3.50  thf('194', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.30/3.50         = (k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['154', '193'])).
% 3.30/3.50  thf('195', plain,
% 3.30/3.50      (![X9 : $i, X10 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 3.30/3.50           = (k3_xboole_0 @ X9 @ X10))),
% 3.30/3.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.30/3.50  thf('196', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 3.30/3.50         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['194', '195'])).
% 3.30/3.50  thf('197', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.30/3.50      inference('demod', [status(thm)], ['184', '185'])).
% 3.30/3.50  thf('198', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.30/3.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.30/3.50  thf('199', plain,
% 3.30/3.50      (((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.30/3.50      inference('demod', [status(thm)], ['196', '197', '198'])).
% 3.30/3.50  thf('200', plain,
% 3.30/3.50      (![X2 : $i, X3 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X2 @ X3)
% 3.30/3.50           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 3.30/3.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.30/3.50  thf('201', plain,
% 3.30/3.50      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['199', '200'])).
% 3.30/3.50  thf('202', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.30/3.50      inference('demod', [status(thm)], ['153', '201'])).
% 3.30/3.50  thf('203', plain,
% 3.30/3.50      (![X21 : $i]:
% 3.30/3.50         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.30/3.50  thf('204', plain,
% 3.30/3.50      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['199', '200'])).
% 3.30/3.50  thf('205', plain,
% 3.30/3.50      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50          = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 3.30/3.50        | ~ (l1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup+', [status(thm)], ['203', '204'])).
% 3.30/3.50  thf('206', plain, ((l1_struct_0 @ sk_A)),
% 3.30/3.50      inference('sup-', [status(thm)], ['8', '9'])).
% 3.30/3.50  thf('207', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.30/3.50      inference('demod', [status(thm)], ['205', '206'])).
% 3.30/3.50  thf('208', plain,
% 3.30/3.50      (![X21 : $i]:
% 3.30/3.50         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 3.30/3.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 3.30/3.50  thf('209', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 3.30/3.50         = (k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['154', '193'])).
% 3.30/3.50  thf('210', plain,
% 3.30/3.50      ((((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.30/3.50          = (k1_xboole_0))
% 3.30/3.50        | ~ (l1_struct_0 @ sk_A))),
% 3.30/3.50      inference('sup+', [status(thm)], ['208', '209'])).
% 3.30/3.50  thf('211', plain, ((l1_struct_0 @ sk_A)),
% 3.30/3.50      inference('sup-', [status(thm)], ['8', '9'])).
% 3.30/3.50  thf('212', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_struct_0 @ sk_A))
% 3.30/3.50         = (k1_xboole_0))),
% 3.30/3.50      inference('demod', [status(thm)], ['210', '211'])).
% 3.30/3.50  thf('213', plain,
% 3.30/3.50      (![X9 : $i, X10 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 3.30/3.50           = (k3_xboole_0 @ X9 @ X10))),
% 3.30/3.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.30/3.50  thf('214', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 3.30/3.50         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_struct_0 @ sk_A)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['212', '213'])).
% 3.30/3.50  thf('215', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.30/3.50      inference('demod', [status(thm)], ['184', '185'])).
% 3.30/3.50  thf('216', plain,
% 3.30/3.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.30/3.50      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.30/3.50  thf('217', plain,
% 3.30/3.50      (((k1_tops_1 @ sk_A @ sk_B)
% 3.30/3.50         = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.30/3.50      inference('demod', [status(thm)], ['214', '215', '216'])).
% 3.30/3.50  thf('218', plain,
% 3.30/3.50      (![X2 : $i, X3 : $i]:
% 3.30/3.50         ((k4_xboole_0 @ X2 @ X3)
% 3.30/3.50           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 3.30/3.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.30/3.50  thf('219', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.30/3.50      inference('sup+', [status(thm)], ['217', '218'])).
% 3.30/3.50  thf('220', plain,
% 3.30/3.50      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.30/3.50      inference('demod', [status(thm)], ['207', '219'])).
% 3.30/3.50  thf('221', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.30/3.50      inference('demod', [status(thm)], ['202', '220'])).
% 3.30/3.50  thf('222', plain,
% 3.30/3.50      (((k3_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 3.30/3.50         (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['118', '125', '126'])).
% 3.30/3.50  thf('223', plain, ((l1_pre_topc @ sk_A)),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('224', plain,
% 3.30/3.50      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50         = (k2_pre_topc @ sk_A @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 3.30/3.50      inference('demod', [status(thm)], ['137', '138', '221', '222', '223'])).
% 3.30/3.50  thf('225', plain,
% 3.30/3.50      (((v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 3.30/3.50        | ((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 3.30/3.50            != (k2_struct_0 @ sk_A)))),
% 3.30/3.50      inference('demod', [status(thm)], ['107', '224'])).
% 3.30/3.50  thf('226', plain,
% 3.30/3.50      (((((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 3.30/3.50           != (k2_struct_0 @ sk_A))
% 3.30/3.50         | (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 3.30/3.50         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.30/3.50      inference('sup-', [status(thm)], ['99', '225'])).
% 3.30/3.50  thf('227', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.30/3.50      inference('sup+', [status(thm)], ['176', '177'])).
% 3.30/3.50  thf('228', plain,
% 3.30/3.50      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 3.30/3.50         | (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 3.30/3.50         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.30/3.50      inference('demod', [status(thm)], ['226', '227'])).
% 3.30/3.50  thf('229', plain,
% 3.30/3.50      (((v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 3.30/3.50         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.30/3.50      inference('simplify', [status(thm)], ['228'])).
% 3.30/3.50  thf('230', plain,
% 3.30/3.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('231', plain,
% 3.30/3.50      (![X29 : $i, X30 : $i]:
% 3.30/3.50         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 3.30/3.50          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 3.30/3.50          | (v2_tops_1 @ X29 @ X30)
% 3.30/3.50          | ~ (l1_pre_topc @ X30))),
% 3.30/3.50      inference('cnf', [status(esa)], [d4_tops_1])).
% 3.30/3.50  thf('232', plain,
% 3.30/3.50      ((~ (l1_pre_topc @ sk_A)
% 3.30/3.50        | (v2_tops_1 @ sk_B @ sk_A)
% 3.30/3.50        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 3.30/3.50      inference('sup-', [status(thm)], ['230', '231'])).
% 3.30/3.50  thf('233', plain, ((l1_pre_topc @ sk_A)),
% 3.30/3.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.50  thf('234', plain,
% 3.30/3.50      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('demod', [status(thm)], ['33', '38'])).
% 3.30/3.50  thf('235', plain,
% 3.30/3.50      (((v2_tops_1 @ sk_B @ sk_A)
% 3.30/3.50        | ~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 3.30/3.50      inference('demod', [status(thm)], ['232', '233', '234'])).
% 3.30/3.50  thf('236', plain,
% 3.30/3.50      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup-', [status(thm)], ['22', '23'])).
% 3.30/3.50  thf('237', plain,
% 3.30/3.50      (((v2_tops_1 @ sk_B @ sk_A)
% 3.30/3.50        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 3.30/3.50      inference('demod', [status(thm)], ['235', '236'])).
% 3.30/3.50  thf('238', plain,
% 3.30/3.50      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 3.30/3.50         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 3.30/3.50      inference('sup+', [status(thm)], ['13', '16'])).
% 3.30/3.50  thf('239', plain,
% 3.30/3.50      (((v2_tops_1 @ sk_B @ sk_A)
% 3.30/3.50        | ~ (v1_tops_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 3.30/3.50      inference('demod', [status(thm)], ['237', '238'])).
% 3.30/3.50  thf('240', plain,
% 3.30/3.50      (((v2_tops_1 @ sk_B @ sk_A))
% 3.30/3.50         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 3.30/3.50      inference('sup-', [status(thm)], ['229', '239'])).
% 3.30/3.50  thf('241', plain,
% 3.30/3.50      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 3.30/3.50      inference('split', [status(esa)], ['0'])).
% 3.30/3.50  thf('242', plain,
% 3.30/3.50      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 3.30/3.50       ((v2_tops_1 @ sk_B @ sk_A))),
% 3.30/3.50      inference('sup-', [status(thm)], ['240', '241'])).
% 3.30/3.50  thf('243', plain, ($false),
% 3.30/3.50      inference('sat_resolution*', [status(thm)], ['1', '97', '98', '242'])).
% 3.30/3.50  
% 3.30/3.50  % SZS output end Refutation
% 3.30/3.50  
% 3.30/3.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
