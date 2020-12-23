%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MKTKD6hdCT

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:43 EST 2020

% Result     : Theorem 5.76s
% Output     : Refutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  237 (9647 expanded)
%              Number of leaves         :   38 (2909 expanded)
%              Depth                    :   33
%              Number of atoms          : 1981 (88135 expanded)
%              Number of equality atoms :  139 (5184 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X21 ) @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ( ( k7_subset_1 @ X31 @ X32 @ X30 )
        = ( k9_subset_1 @ X31 @ X32 @ ( k3_subset_1 @ X31 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('15',plain,(
    ! [X43: $i] :
      ( ( l1_struct_0 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
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
    inference('sup-',[status(thm)],['14','15'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['8','25'])).

thf('27',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('35',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k9_subset_1 @ X29 @ X27 @ X28 )
        = ( k3_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['26','37'])).

thf('39',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','38'])).

thf('40',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('42',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('43',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('62',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('63',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('64',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('71',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('75',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('77',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('82',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','80','81'])).

thf('83',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['67'])).

thf('85',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('87',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('89',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','89'])).

thf('91',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','90'])).

thf('92',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('93',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','89'])).

thf('94',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('97',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','98'])).

thf('100',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('101',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('102',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['100','105'])).

thf('107',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('108',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('110',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('111',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('113',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('114',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('115',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['111','112','113','114'])).

thf('116',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','89'])).

thf('117',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('120',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','121'])).

thf('123',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['117','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('125',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('126',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('127',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('129',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('131',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124','131'])).

thf('133',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('135',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['133','140'])).

thf('142',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('143',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('144',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','89'])).

thf('146',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('148',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('150',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','148','149'])).

thf('151',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['99','150'])).

thf('152',plain,
    ( ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','151'])).

thf('153',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('154',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['155'])).

thf('157',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('158',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v4_pre_topc @ X41 @ X42 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k2_struct_0 @ X42 ) @ X41 ) @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('159',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['156','161'])).

thf('163',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['154','162'])).

thf('164',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('165',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','89'])).

thf('166',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('167',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('168',plain,
    ( ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('170',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['165','170'])).

thf('172',plain,
    ( ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['164','171'])).

thf('173',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('174',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['163','174'])).

thf('176',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['155'])).

thf('177',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('178',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['62','89'])).

thf('179',plain,(
    ! [X40: $i] :
      ( ( ( k2_struct_0 @ X40 )
        = ( u1_struct_0 @ X40 ) )
      | ~ ( l1_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('180',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['155'])).

thf('181',plain,
    ( ( ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('183',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['178','183'])).

thf('185',plain,
    ( ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['177','184'])).

thf('186',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('187',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('189',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k2_struct_0 @ X42 ) @ X41 ) @ X42 )
      | ( v4_pre_topc @ X41 @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('190',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['187','193'])).

thf('195',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('196',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','175','176','196'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MKTKD6hdCT
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 5.76/6.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.76/6.01  % Solved by: fo/fo7.sh
% 5.76/6.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.76/6.01  % done 4641 iterations in 5.554s
% 5.76/6.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.76/6.01  % SZS output start Refutation
% 5.76/6.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.76/6.01  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.76/6.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.76/6.01  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.76/6.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.76/6.01  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.76/6.01  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.76/6.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.76/6.01  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.76/6.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.76/6.01  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 5.76/6.01  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.76/6.01  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.76/6.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.76/6.01  thf(sk_A_type, type, sk_A: $i).
% 5.76/6.01  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.76/6.01  thf(sk_B_type, type, sk_B: $i).
% 5.76/6.01  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.76/6.01  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 5.76/6.01  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 5.76/6.01  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.76/6.01  thf(t29_tops_1, conjecture,
% 5.76/6.01    (![A:$i]:
% 5.76/6.01     ( ( l1_pre_topc @ A ) =>
% 5.76/6.01       ( ![B:$i]:
% 5.76/6.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.76/6.01           ( ( v4_pre_topc @ B @ A ) <=>
% 5.76/6.01             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 5.76/6.01  thf(zf_stmt_0, negated_conjecture,
% 5.76/6.01    (~( ![A:$i]:
% 5.76/6.01        ( ( l1_pre_topc @ A ) =>
% 5.76/6.01          ( ![B:$i]:
% 5.76/6.01            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.76/6.01              ( ( v4_pre_topc @ B @ A ) <=>
% 5.76/6.01                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 5.76/6.01    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 5.76/6.01  thf('0', plain,
% 5.76/6.01      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.76/6.01        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.76/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.76/6.01  thf('1', plain,
% 5.76/6.01      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 5.76/6.01       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.76/6.01      inference('split', [status(esa)], ['0'])).
% 5.76/6.01  thf(d3_struct_0, axiom,
% 5.76/6.01    (![A:$i]:
% 5.76/6.01     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.76/6.01  thf('2', plain,
% 5.76/6.01      (![X40 : $i]:
% 5.76/6.01         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 5.76/6.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.76/6.01  thf(dt_k2_subset_1, axiom,
% 5.76/6.01    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.76/6.01  thf('3', plain,
% 5.76/6.01      (![X21 : $i]: (m1_subset_1 @ (k2_subset_1 @ X21) @ (k1_zfmisc_1 @ X21))),
% 5.76/6.01      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 5.76/6.01  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.76/6.01  thf('4', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 5.76/6.01      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.76/6.01  thf('5', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 5.76/6.01      inference('demod', [status(thm)], ['3', '4'])).
% 5.76/6.01  thf('6', plain,
% 5.76/6.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.76/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.76/6.01  thf(t32_subset_1, axiom,
% 5.76/6.01    (![A:$i,B:$i]:
% 5.76/6.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.76/6.01       ( ![C:$i]:
% 5.76/6.01         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.76/6.01           ( ( k7_subset_1 @ A @ B @ C ) =
% 5.76/6.01             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 5.76/6.01  thf('7', plain,
% 5.76/6.01      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.76/6.01         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31))
% 5.76/6.01          | ((k7_subset_1 @ X31 @ X32 @ X30)
% 5.76/6.01              = (k9_subset_1 @ X31 @ X32 @ (k3_subset_1 @ X31 @ X30)))
% 5.76/6.01          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 5.76/6.01      inference('cnf', [status(esa)], [t32_subset_1])).
% 5.76/6.01  thf('8', plain,
% 5.76/6.01      (![X0 : $i]:
% 5.76/6.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.76/6.01          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 5.76/6.01              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 5.76/6.01                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 5.76/6.01      inference('sup-', [status(thm)], ['6', '7'])).
% 5.76/6.01  thf('9', plain,
% 5.76/6.01      (![X40 : $i]:
% 5.76/6.01         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 5.76/6.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.76/6.01  thf('10', plain,
% 5.76/6.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.76/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.76/6.01  thf(d5_subset_1, axiom,
% 5.76/6.01    (![A:$i,B:$i]:
% 5.76/6.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.76/6.01       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 5.76/6.01  thf('11', plain,
% 5.76/6.01      (![X19 : $i, X20 : $i]:
% 5.76/6.01         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 5.76/6.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 5.76/6.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.76/6.01  thf('12', plain,
% 5.76/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.76/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.76/6.01      inference('sup-', [status(thm)], ['10', '11'])).
% 5.76/6.01  thf('13', plain,
% 5.76/6.01      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.76/6.01          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.76/6.01        | ~ (l1_struct_0 @ sk_A))),
% 5.76/6.01      inference('sup+', [status(thm)], ['9', '12'])).
% 5.76/6.01  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 5.76/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.76/6.01  thf(dt_l1_pre_topc, axiom,
% 5.76/6.01    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 5.76/6.01  thf('15', plain,
% 5.76/6.01      (![X43 : $i]: ((l1_struct_0 @ X43) | ~ (l1_pre_topc @ X43))),
% 5.76/6.01      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.76/6.01  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 5.76/6.01      inference('sup-', [status(thm)], ['14', '15'])).
% 5.76/6.01  thf('17', plain,
% 5.76/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.76/6.01         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.76/6.01      inference('demod', [status(thm)], ['13', '16'])).
% 5.76/6.01  thf('18', plain,
% 5.76/6.01      (![X40 : $i]:
% 5.76/6.01         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 5.76/6.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.76/6.01  thf('19', plain,
% 5.76/6.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.76/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.76/6.01  thf('20', plain,
% 5.76/6.01      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 5.76/6.01        | ~ (l1_struct_0 @ sk_A))),
% 5.76/6.01      inference('sup+', [status(thm)], ['18', '19'])).
% 5.76/6.01  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 5.76/6.01      inference('sup-', [status(thm)], ['14', '15'])).
% 5.76/6.01  thf('22', plain,
% 5.76/6.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 5.76/6.01      inference('demod', [status(thm)], ['20', '21'])).
% 5.76/6.01  thf('23', plain,
% 5.76/6.01      (![X19 : $i, X20 : $i]:
% 5.76/6.01         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 5.76/6.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 5.76/6.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.76/6.01  thf('24', plain,
% 5.76/6.01      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.76/6.01         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.76/6.01      inference('sup-', [status(thm)], ['22', '23'])).
% 5.76/6.01  thf('25', plain,
% 5.76/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.76/6.01         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.76/6.01      inference('demod', [status(thm)], ['17', '24'])).
% 5.76/6.01  thf('26', plain,
% 5.76/6.01      (![X0 : $i]:
% 5.76/6.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.76/6.01          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 5.76/6.01              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 5.76/6.01                 (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 5.76/6.01      inference('demod', [status(thm)], ['8', '25'])).
% 5.76/6.01  thf('27', plain,
% 5.76/6.01      (![X40 : $i]:
% 5.76/6.01         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 5.76/6.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.76/6.01  thf('28', plain,
% 5.76/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.76/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.76/6.01      inference('sup-', [status(thm)], ['10', '11'])).
% 5.76/6.01  thf(t36_xboole_1, axiom,
% 5.76/6.01    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 5.76/6.01  thf('29', plain,
% 5.76/6.01      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 5.76/6.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.76/6.01  thf('30', plain,
% 5.76/6.01      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.76/6.01        (u1_struct_0 @ sk_A))),
% 5.76/6.01      inference('sup+', [status(thm)], ['28', '29'])).
% 5.76/6.01  thf(t3_subset, axiom,
% 5.76/6.01    (![A:$i,B:$i]:
% 5.76/6.01     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.76/6.01  thf('31', plain,
% 5.76/6.01      (![X34 : $i, X36 : $i]:
% 5.76/6.01         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 5.76/6.01      inference('cnf', [status(esa)], [t3_subset])).
% 5.76/6.01  thf('32', plain,
% 5.76/6.01      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.76/6.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.76/6.01      inference('sup-', [status(thm)], ['30', '31'])).
% 5.76/6.01  thf('33', plain,
% 5.76/6.01      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.76/6.01         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.76/6.01        | ~ (l1_struct_0 @ sk_A))),
% 5.76/6.01      inference('sup+', [status(thm)], ['27', '32'])).
% 5.76/6.01  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 5.76/6.01      inference('sup-', [status(thm)], ['14', '15'])).
% 5.76/6.01  thf('35', plain,
% 5.76/6.01      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.76/6.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.76/6.01      inference('demod', [status(thm)], ['33', '34'])).
% 5.76/6.01  thf(redefinition_k9_subset_1, axiom,
% 5.76/6.01    (![A:$i,B:$i,C:$i]:
% 5.76/6.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.76/6.01       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 5.76/6.01  thf('36', plain,
% 5.76/6.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.76/6.01         (((k9_subset_1 @ X29 @ X27 @ X28) = (k3_xboole_0 @ X27 @ X28))
% 5.76/6.01          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 5.76/6.01      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 5.76/6.01  thf('37', plain,
% 5.76/6.01      (![X0 : $i]:
% 5.76/6.01         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 5.76/6.01           (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.76/6.01           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.76/6.01      inference('sup-', [status(thm)], ['35', '36'])).
% 5.76/6.01  thf('38', plain,
% 5.76/6.01      (![X0 : $i]:
% 5.76/6.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.76/6.01          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 5.76/6.01              = (k3_xboole_0 @ X0 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 5.76/6.01      inference('demod', [status(thm)], ['26', '37'])).
% 5.84/6.01  thf('39', plain,
% 5.84/6.01      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.84/6.01      inference('sup-', [status(thm)], ['5', '38'])).
% 5.84/6.01  thf('40', plain,
% 5.84/6.01      (![X40 : $i]:
% 5.84/6.01         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 5.84/6.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.84/6.01  thf('41', plain,
% 5.84/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('sup-', [status(thm)], ['10', '11'])).
% 5.84/6.01  thf('42', plain,
% 5.84/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('demod', [status(thm)], ['17', '24'])).
% 5.84/6.01  thf('43', plain,
% 5.84/6.01      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('demod', [status(thm)], ['41', '42'])).
% 5.84/6.01  thf(t48_xboole_1, axiom,
% 5.84/6.01    (![A:$i,B:$i]:
% 5.84/6.01     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 5.84/6.01  thf('44', plain,
% 5.84/6.01      (![X16 : $i, X17 : $i]:
% 5.84/6.01         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.84/6.01           = (k3_xboole_0 @ X16 @ X17))),
% 5.84/6.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.84/6.01  thf('45', plain,
% 5.84/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.84/6.01         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('sup+', [status(thm)], ['43', '44'])).
% 5.84/6.01  thf(commutativity_k3_xboole_0, axiom,
% 5.84/6.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.84/6.01  thf('46', plain,
% 5.84/6.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.84/6.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.84/6.01  thf('47', plain,
% 5.84/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.84/6.01         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.84/6.01      inference('demod', [status(thm)], ['45', '46'])).
% 5.84/6.01  thf('48', plain,
% 5.84/6.01      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 5.84/6.01          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.84/6.01          = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 5.84/6.01        | ~ (l1_struct_0 @ sk_A))),
% 5.84/6.01      inference('sup+', [status(thm)], ['40', '47'])).
% 5.84/6.01  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 5.84/6.01      inference('sup-', [status(thm)], ['14', '15'])).
% 5.84/6.01  thf('50', plain,
% 5.84/6.01      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 5.84/6.01         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.84/6.01         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.84/6.01      inference('demod', [status(thm)], ['48', '49'])).
% 5.84/6.01  thf('51', plain,
% 5.84/6.01      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('sup-', [status(thm)], ['22', '23'])).
% 5.84/6.01  thf('52', plain,
% 5.84/6.01      (![X16 : $i, X17 : $i]:
% 5.84/6.01         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.84/6.01           = (k3_xboole_0 @ X16 @ X17))),
% 5.84/6.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.84/6.01  thf('53', plain,
% 5.84/6.01      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 5.84/6.01         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.84/6.01         = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('sup+', [status(thm)], ['51', '52'])).
% 5.84/6.01  thf('54', plain,
% 5.84/6.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.84/6.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.84/6.01  thf('55', plain,
% 5.84/6.01      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 5.84/6.01         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.84/6.01         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('demod', [status(thm)], ['53', '54'])).
% 5.84/6.01  thf('56', plain,
% 5.84/6.01      (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.84/6.01         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('sup+', [status(thm)], ['50', '55'])).
% 5.84/6.01  thf('57', plain,
% 5.84/6.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.84/6.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.84/6.01  thf(t100_xboole_1, axiom,
% 5.84/6.01    (![A:$i,B:$i]:
% 5.84/6.01     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.84/6.01  thf('58', plain,
% 5.84/6.01      (![X11 : $i, X12 : $i]:
% 5.84/6.01         ((k4_xboole_0 @ X11 @ X12)
% 5.84/6.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 5.84/6.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.84/6.01  thf('59', plain,
% 5.84/6.01      (![X0 : $i, X1 : $i]:
% 5.84/6.01         ((k4_xboole_0 @ X0 @ X1)
% 5.84/6.01           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.84/6.01      inference('sup+', [status(thm)], ['57', '58'])).
% 5.84/6.01  thf('60', plain,
% 5.84/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01            (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))))),
% 5.84/6.01      inference('sup+', [status(thm)], ['56', '59'])).
% 5.84/6.01  thf('61', plain,
% 5.84/6.01      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('demod', [status(thm)], ['41', '42'])).
% 5.84/6.01  thf('62', plain,
% 5.84/6.01      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01            (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))))),
% 5.84/6.01      inference('demod', [status(thm)], ['60', '61'])).
% 5.84/6.01  thf(d5_xboole_0, axiom,
% 5.84/6.01    (![A:$i,B:$i,C:$i]:
% 5.84/6.01     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 5.84/6.01       ( ![D:$i]:
% 5.84/6.01         ( ( r2_hidden @ D @ C ) <=>
% 5.84/6.01           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 5.84/6.01  thf('63', plain,
% 5.84/6.01      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.84/6.01         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.84/6.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 5.84/6.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.84/6.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.84/6.01  thf(t3_boole, axiom,
% 5.84/6.01    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.84/6.01  thf('64', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 5.84/6.01      inference('cnf', [status(esa)], [t3_boole])).
% 5.84/6.01  thf('65', plain,
% 5.84/6.01      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 5.84/6.01         (~ (r2_hidden @ X6 @ X5)
% 5.84/6.01          | ~ (r2_hidden @ X6 @ X4)
% 5.84/6.01          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 5.84/6.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.84/6.01  thf('66', plain,
% 5.84/6.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 5.84/6.01         (~ (r2_hidden @ X6 @ X4)
% 5.84/6.01          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 5.84/6.01      inference('simplify', [status(thm)], ['65'])).
% 5.84/6.01  thf('67', plain,
% 5.84/6.01      (![X0 : $i, X1 : $i]:
% 5.84/6.01         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 5.84/6.01      inference('sup-', [status(thm)], ['64', '66'])).
% 5.84/6.01  thf('68', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.84/6.01      inference('condensation', [status(thm)], ['67'])).
% 5.84/6.01  thf('69', plain,
% 5.84/6.01      (![X0 : $i, X1 : $i]:
% 5.84/6.01         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 5.84/6.01          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 5.84/6.01      inference('sup-', [status(thm)], ['63', '68'])).
% 5.84/6.01  thf('70', plain,
% 5.84/6.01      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.84/6.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.01  thf(l3_subset_1, axiom,
% 5.84/6.01    (![A:$i,B:$i]:
% 5.84/6.01     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.84/6.01       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 5.84/6.01  thf('71', plain,
% 5.84/6.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.84/6.01         (~ (r2_hidden @ X24 @ X25)
% 5.84/6.01          | (r2_hidden @ X24 @ X26)
% 5.84/6.01          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 5.84/6.01      inference('cnf', [status(esa)], [l3_subset_1])).
% 5.84/6.01  thf('72', plain,
% 5.84/6.01      (![X0 : $i]:
% 5.84/6.01         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 5.84/6.01      inference('sup-', [status(thm)], ['70', '71'])).
% 5.84/6.01  thf('73', plain,
% 5.84/6.01      (![X0 : $i]:
% 5.84/6.01         (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ X0))
% 5.84/6.01          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ sk_B) @ 
% 5.84/6.01             (u1_struct_0 @ sk_A)))),
% 5.84/6.01      inference('sup-', [status(thm)], ['69', '72'])).
% 5.84/6.01  thf('74', plain,
% 5.84/6.01      (![X3 : $i, X4 : $i, X7 : $i]:
% 5.84/6.01         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 5.84/6.01          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 5.84/6.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 5.84/6.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 5.84/6.01  thf('75', plain,
% 5.84/6.01      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 5.84/6.01        | (r2_hidden @ (sk_D @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.84/6.01           k1_xboole_0)
% 5.84/6.01        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 5.84/6.01      inference('sup-', [status(thm)], ['73', '74'])).
% 5.84/6.01  thf('76', plain,
% 5.84/6.01      (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.84/6.01         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('sup+', [status(thm)], ['50', '55'])).
% 5.84/6.01  thf('77', plain,
% 5.84/6.01      (![X11 : $i, X12 : $i]:
% 5.84/6.01         ((k4_xboole_0 @ X11 @ X12)
% 5.84/6.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 5.84/6.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.84/6.01  thf('78', plain,
% 5.84/6.01      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.84/6.01         = (k5_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))))),
% 5.84/6.01      inference('sup+', [status(thm)], ['76', '77'])).
% 5.84/6.01  thf('79', plain,
% 5.84/6.01      (![X11 : $i, X12 : $i]:
% 5.84/6.01         ((k4_xboole_0 @ X11 @ X12)
% 5.84/6.01           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 5.84/6.01      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.84/6.01  thf('80', plain,
% 5.84/6.01      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.84/6.01         = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('demod', [status(thm)], ['78', '79'])).
% 5.84/6.01  thf('81', plain,
% 5.84/6.01      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.84/6.01         = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('demod', [status(thm)], ['78', '79'])).
% 5.84/6.01  thf('82', plain,
% 5.84/6.01      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))
% 5.84/6.01        | (r2_hidden @ (sk_D @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.84/6.01           k1_xboole_0)
% 5.84/6.01        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))))),
% 5.84/6.01      inference('demod', [status(thm)], ['75', '80', '81'])).
% 5.84/6.01  thf('83', plain,
% 5.84/6.01      (((r2_hidden @ (sk_D @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 5.84/6.01         k1_xboole_0)
% 5.84/6.01        | ((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))))),
% 5.84/6.01      inference('simplify', [status(thm)], ['82'])).
% 5.84/6.01  thf('84', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.84/6.01      inference('condensation', [status(thm)], ['67'])).
% 5.84/6.01  thf('85', plain,
% 5.84/6.01      (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('clc', [status(thm)], ['83', '84'])).
% 5.84/6.01  thf('86', plain,
% 5.84/6.01      (![X16 : $i, X17 : $i]:
% 5.84/6.01         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.84/6.01           = (k3_xboole_0 @ X16 @ X17))),
% 5.84/6.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.84/6.01  thf('87', plain,
% 5.84/6.01      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 5.84/6.01         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('sup+', [status(thm)], ['85', '86'])).
% 5.84/6.01  thf('88', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 5.84/6.01      inference('cnf', [status(esa)], [t3_boole])).
% 5.84/6.01  thf('89', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('demod', [status(thm)], ['87', '88'])).
% 5.84/6.01  thf('90', plain,
% 5.84/6.01      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('demod', [status(thm)], ['62', '89'])).
% 5.84/6.01  thf('91', plain,
% 5.84/6.01      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 5.84/6.01      inference('demod', [status(thm)], ['39', '90'])).
% 5.84/6.01  thf('92', plain,
% 5.84/6.01      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('sup-', [status(thm)], ['22', '23'])).
% 5.84/6.01  thf('93', plain,
% 5.84/6.01      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('demod', [status(thm)], ['62', '89'])).
% 5.84/6.01  thf('94', plain,
% 5.84/6.01      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('demod', [status(thm)], ['92', '93'])).
% 5.84/6.01  thf('95', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('demod', [status(thm)], ['87', '88'])).
% 5.84/6.01  thf('96', plain,
% 5.84/6.01      (![X0 : $i, X1 : $i]:
% 5.84/6.01         ((k4_xboole_0 @ X0 @ X1)
% 5.84/6.01           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.84/6.01      inference('sup+', [status(thm)], ['57', '58'])).
% 5.84/6.01  thf('97', plain,
% 5.84/6.01      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('sup+', [status(thm)], ['95', '96'])).
% 5.84/6.01  thf('98', plain,
% 5.84/6.01      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.01      inference('sup+', [status(thm)], ['94', '97'])).
% 5.84/6.01  thf('99', plain,
% 5.84/6.01      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.01         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01            (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.84/6.01      inference('demod', [status(thm)], ['91', '98'])).
% 5.84/6.01  thf('100', plain,
% 5.84/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.84/6.01         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.84/6.01      inference('demod', [status(thm)], ['45', '46'])).
% 5.84/6.01  thf('101', plain,
% 5.84/6.01      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 5.84/6.01      inference('cnf', [status(esa)], [t36_xboole_1])).
% 5.84/6.01  thf('102', plain,
% 5.84/6.01      (![X34 : $i, X36 : $i]:
% 5.84/6.01         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 5.84/6.01      inference('cnf', [status(esa)], [t3_subset])).
% 5.84/6.01  thf('103', plain,
% 5.84/6.01      (![X0 : $i, X1 : $i]:
% 5.84/6.01         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 5.84/6.01      inference('sup-', [status(thm)], ['101', '102'])).
% 5.84/6.01  thf('104', plain,
% 5.84/6.01      (![X19 : $i, X20 : $i]:
% 5.84/6.01         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 5.84/6.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 5.84/6.01      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.84/6.01  thf('105', plain,
% 5.84/6.01      (![X0 : $i, X1 : $i]:
% 5.84/6.01         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 5.84/6.01           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.84/6.01      inference('sup-', [status(thm)], ['103', '104'])).
% 5.84/6.01  thf('106', plain,
% 5.84/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 5.84/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01            (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 5.84/6.01      inference('sup+', [status(thm)], ['100', '105'])).
% 5.84/6.01  thf('107', plain,
% 5.84/6.01      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.84/6.01         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.84/6.01      inference('demod', [status(thm)], ['45', '46'])).
% 5.84/6.01  thf('108', plain,
% 5.84/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01         (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 5.84/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01            (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 5.84/6.01      inference('demod', [status(thm)], ['106', '107'])).
% 5.84/6.01  thf('109', plain,
% 5.84/6.01      (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.84/6.01         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('sup+', [status(thm)], ['50', '55'])).
% 5.84/6.01  thf('110', plain,
% 5.84/6.01      (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.84/6.01         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('sup+', [status(thm)], ['50', '55'])).
% 5.84/6.01  thf('111', plain,
% 5.84/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01         (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))
% 5.84/6.01         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.01            (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A))))),
% 5.84/6.01      inference('demod', [status(thm)], ['108', '109', '110'])).
% 5.84/6.01  thf('112', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.01      inference('demod', [status(thm)], ['87', '88'])).
% 5.84/6.01  thf('113', plain,
% 5.84/6.01      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['17', '24'])).
% 5.84/6.02  thf('114', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.02      inference('demod', [status(thm)], ['87', '88'])).
% 5.84/6.02  thf('115', plain,
% 5.84/6.02      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['111', '112', '113', '114'])).
% 5.84/6.02  thf('116', plain,
% 5.84/6.02      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['62', '89'])).
% 5.84/6.02  thf('117', plain,
% 5.84/6.02      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['115', '116'])).
% 5.84/6.02  thf('118', plain,
% 5.84/6.02      (![X16 : $i, X17 : $i]:
% 5.84/6.02         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.84/6.02           = (k3_xboole_0 @ X16 @ X17))),
% 5.84/6.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.84/6.02  thf('119', plain,
% 5.84/6.02      (![X0 : $i, X1 : $i]:
% 5.84/6.02         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 5.84/6.02           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 5.84/6.02      inference('sup-', [status(thm)], ['103', '104'])).
% 5.84/6.02  thf('120', plain,
% 5.84/6.02      (![X16 : $i, X17 : $i]:
% 5.84/6.02         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.84/6.02           = (k3_xboole_0 @ X16 @ X17))),
% 5.84/6.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.84/6.02  thf('121', plain,
% 5.84/6.02      (![X0 : $i, X1 : $i]:
% 5.84/6.02         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 5.84/6.02           = (k3_xboole_0 @ X1 @ X0))),
% 5.84/6.02      inference('sup+', [status(thm)], ['119', '120'])).
% 5.84/6.02  thf('122', plain,
% 5.84/6.02      (![X0 : $i, X1 : $i]:
% 5.84/6.02         ((k3_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 5.84/6.02           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.84/6.02      inference('sup+', [status(thm)], ['118', '121'])).
% 5.84/6.02  thf('123', plain,
% 5.84/6.02      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.02         (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 5.84/6.02         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.02            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 5.84/6.02      inference('sup+', [status(thm)], ['117', '122'])).
% 5.84/6.02  thf('124', plain,
% 5.84/6.02      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.84/6.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.84/6.02  thf('125', plain,
% 5.84/6.02      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))
% 5.84/6.02         = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.02      inference('demod', [status(thm)], ['78', '79'])).
% 5.84/6.02  thf('126', plain,
% 5.84/6.02      (((k1_xboole_0) = (k4_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)))),
% 5.84/6.02      inference('clc', [status(thm)], ['83', '84'])).
% 5.84/6.02  thf('127', plain,
% 5.84/6.02      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 5.84/6.02      inference('demod', [status(thm)], ['125', '126'])).
% 5.84/6.02  thf('128', plain,
% 5.84/6.02      (![X16 : $i, X17 : $i]:
% 5.84/6.02         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.84/6.02           = (k3_xboole_0 @ X16 @ X17))),
% 5.84/6.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.84/6.02  thf('129', plain,
% 5.84/6.02      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 5.84/6.02         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.84/6.02      inference('sup+', [status(thm)], ['127', '128'])).
% 5.84/6.02  thf('130', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 5.84/6.02      inference('cnf', [status(esa)], [t3_boole])).
% 5.84/6.02  thf('131', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.84/6.02      inference('demod', [status(thm)], ['129', '130'])).
% 5.84/6.02  thf('132', plain,
% 5.84/6.02      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.02            (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 5.84/6.02      inference('demod', [status(thm)], ['123', '124', '131'])).
% 5.84/6.02  thf('133', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.84/6.02      inference('demod', [status(thm)], ['129', '130'])).
% 5.84/6.02  thf('134', plain,
% 5.84/6.02      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.84/6.02      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.84/6.02  thf('135', plain,
% 5.84/6.02      (![X16 : $i, X17 : $i]:
% 5.84/6.02         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 5.84/6.02           = (k3_xboole_0 @ X16 @ X17))),
% 5.84/6.02      inference('cnf', [status(esa)], [t48_xboole_1])).
% 5.84/6.02  thf('136', plain,
% 5.84/6.02      (![X0 : $i, X1 : $i]:
% 5.84/6.02         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 5.84/6.02      inference('sup-', [status(thm)], ['101', '102'])).
% 5.84/6.02  thf('137', plain,
% 5.84/6.02      (![X0 : $i, X1 : $i]:
% 5.84/6.02         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 5.84/6.02      inference('sup+', [status(thm)], ['135', '136'])).
% 5.84/6.02  thf('138', plain,
% 5.84/6.02      (![X0 : $i, X1 : $i]:
% 5.84/6.02         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 5.84/6.02      inference('sup+', [status(thm)], ['134', '137'])).
% 5.84/6.02  thf('139', plain,
% 5.84/6.02      (![X19 : $i, X20 : $i]:
% 5.84/6.02         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 5.84/6.02          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 5.84/6.02      inference('cnf', [status(esa)], [d5_subset_1])).
% 5.84/6.02  thf('140', plain,
% 5.84/6.02      (![X0 : $i, X1 : $i]:
% 5.84/6.02         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 5.84/6.02           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.84/6.02      inference('sup-', [status(thm)], ['138', '139'])).
% 5.84/6.02  thf('141', plain,
% 5.84/6.02      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.02         (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 5.84/6.02         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('sup+', [status(thm)], ['133', '140'])).
% 5.84/6.02  thf('142', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 5.84/6.02      inference('demod', [status(thm)], ['129', '130'])).
% 5.84/6.02  thf('143', plain,
% 5.84/6.02      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['41', '42'])).
% 5.84/6.02  thf('144', plain,
% 5.84/6.02      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['141', '142', '143'])).
% 5.84/6.02  thf('145', plain,
% 5.84/6.02      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['62', '89'])).
% 5.84/6.02  thf('146', plain,
% 5.84/6.02      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['144', '145'])).
% 5.84/6.02  thf('147', plain,
% 5.84/6.02      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('sup+', [status(thm)], ['94', '97'])).
% 5.84/6.02  thf('148', plain,
% 5.84/6.02      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['146', '147'])).
% 5.84/6.02  thf('149', plain,
% 5.84/6.02      (((k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('sup+', [status(thm)], ['94', '97'])).
% 5.84/6.02  thf('150', plain,
% 5.84/6.02      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 5.84/6.02            (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 5.84/6.02      inference('demod', [status(thm)], ['132', '148', '149'])).
% 5.84/6.02  thf('151', plain,
% 5.84/6.02      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('sup+', [status(thm)], ['99', '150'])).
% 5.84/6.02  thf('152', plain,
% 5.84/6.02      ((((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 5.84/6.02        | ~ (l1_struct_0 @ sk_A))),
% 5.84/6.02      inference('sup+', [status(thm)], ['2', '151'])).
% 5.84/6.02  thf('153', plain, ((l1_struct_0 @ sk_A)),
% 5.84/6.02      inference('sup-', [status(thm)], ['14', '15'])).
% 5.84/6.02  thf('154', plain,
% 5.84/6.02      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['152', '153'])).
% 5.84/6.02  thf('155', plain,
% 5.84/6.02      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.84/6.02        | (v4_pre_topc @ sk_B @ sk_A))),
% 5.84/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.02  thf('156', plain,
% 5.84/6.02      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.84/6.02      inference('split', [status(esa)], ['155'])).
% 5.84/6.02  thf('157', plain,
% 5.84/6.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.84/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.02  thf(d6_pre_topc, axiom,
% 5.84/6.02    (![A:$i]:
% 5.84/6.02     ( ( l1_pre_topc @ A ) =>
% 5.84/6.02       ( ![B:$i]:
% 5.84/6.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.84/6.02           ( ( v4_pre_topc @ B @ A ) <=>
% 5.84/6.02             ( v3_pre_topc @
% 5.84/6.02               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 5.84/6.02               A ) ) ) ) ))).
% 5.84/6.02  thf('158', plain,
% 5.84/6.02      (![X41 : $i, X42 : $i]:
% 5.84/6.02         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 5.84/6.02          | ~ (v4_pre_topc @ X41 @ X42)
% 5.84/6.02          | (v3_pre_topc @ 
% 5.84/6.02             (k7_subset_1 @ (u1_struct_0 @ X42) @ (k2_struct_0 @ X42) @ X41) @ 
% 5.84/6.02             X42)
% 5.84/6.02          | ~ (l1_pre_topc @ X42))),
% 5.84/6.02      inference('cnf', [status(esa)], [d6_pre_topc])).
% 5.84/6.02  thf('159', plain,
% 5.84/6.02      ((~ (l1_pre_topc @ sk_A)
% 5.84/6.02        | (v3_pre_topc @ 
% 5.84/6.02           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.84/6.02           sk_A)
% 5.84/6.02        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.84/6.02      inference('sup-', [status(thm)], ['157', '158'])).
% 5.84/6.02  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 5.84/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.02  thf('161', plain,
% 5.84/6.02      (((v3_pre_topc @ 
% 5.84/6.02         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.84/6.02         sk_A)
% 5.84/6.02        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 5.84/6.02      inference('demod', [status(thm)], ['159', '160'])).
% 5.84/6.02  thf('162', plain,
% 5.84/6.02      (((v3_pre_topc @ 
% 5.84/6.02         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 5.84/6.02         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.84/6.02      inference('sup-', [status(thm)], ['156', '161'])).
% 5.84/6.02  thf('163', plain,
% 5.84/6.02      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.84/6.02         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 5.84/6.02      inference('sup+', [status(thm)], ['154', '162'])).
% 5.84/6.02  thf('164', plain,
% 5.84/6.02      (![X40 : $i]:
% 5.84/6.02         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 5.84/6.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.84/6.02  thf('165', plain,
% 5.84/6.02      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['62', '89'])).
% 5.84/6.02  thf('166', plain,
% 5.84/6.02      (![X40 : $i]:
% 5.84/6.02         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 5.84/6.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.84/6.02  thf('167', plain,
% 5.84/6.02      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.84/6.02         <= (~
% 5.84/6.02             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('split', [status(esa)], ['0'])).
% 5.84/6.02  thf('168', plain,
% 5.84/6.02      (((~ (v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.84/6.02         | ~ (l1_struct_0 @ sk_A)))
% 5.84/6.02         <= (~
% 5.84/6.02             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('sup-', [status(thm)], ['166', '167'])).
% 5.84/6.02  thf('169', plain, ((l1_struct_0 @ sk_A)),
% 5.84/6.02      inference('sup-', [status(thm)], ['14', '15'])).
% 5.84/6.02  thf('170', plain,
% 5.84/6.02      ((~ (v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.84/6.02         <= (~
% 5.84/6.02             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('demod', [status(thm)], ['168', '169'])).
% 5.84/6.02  thf('171', plain,
% 5.84/6.02      ((~ (v3_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.84/6.02         <= (~
% 5.84/6.02             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('sup-', [status(thm)], ['165', '170'])).
% 5.84/6.02  thf('172', plain,
% 5.84/6.02      (((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.84/6.02         | ~ (l1_struct_0 @ sk_A)))
% 5.84/6.02         <= (~
% 5.84/6.02             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('sup-', [status(thm)], ['164', '171'])).
% 5.84/6.02  thf('173', plain, ((l1_struct_0 @ sk_A)),
% 5.84/6.02      inference('sup-', [status(thm)], ['14', '15'])).
% 5.84/6.02  thf('174', plain,
% 5.84/6.02      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.84/6.02         <= (~
% 5.84/6.02             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('demod', [status(thm)], ['172', '173'])).
% 5.84/6.02  thf('175', plain,
% 5.84/6.02      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 5.84/6.02       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 5.84/6.02      inference('sup-', [status(thm)], ['163', '174'])).
% 5.84/6.02  thf('176', plain,
% 5.84/6.02      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 5.84/6.02       ((v4_pre_topc @ sk_B @ sk_A))),
% 5.84/6.02      inference('split', [status(esa)], ['155'])).
% 5.84/6.02  thf('177', plain,
% 5.84/6.02      (![X40 : $i]:
% 5.84/6.02         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 5.84/6.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.84/6.02  thf('178', plain,
% 5.84/6.02      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['62', '89'])).
% 5.84/6.02  thf('179', plain,
% 5.84/6.02      (![X40 : $i]:
% 5.84/6.02         (((k2_struct_0 @ X40) = (u1_struct_0 @ X40)) | ~ (l1_struct_0 @ X40))),
% 5.84/6.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.84/6.02  thf('180', plain,
% 5.84/6.02      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.84/6.02         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('split', [status(esa)], ['155'])).
% 5.84/6.02  thf('181', plain,
% 5.84/6.02      ((((v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.84/6.02         | ~ (l1_struct_0 @ sk_A)))
% 5.84/6.02         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('sup+', [status(thm)], ['179', '180'])).
% 5.84/6.02  thf('182', plain, ((l1_struct_0 @ sk_A)),
% 5.84/6.02      inference('sup-', [status(thm)], ['14', '15'])).
% 5.84/6.02  thf('183', plain,
% 5.84/6.02      (((v3_pre_topc @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.84/6.02         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('demod', [status(thm)], ['181', '182'])).
% 5.84/6.02  thf('184', plain,
% 5.84/6.02      (((v3_pre_topc @ (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.84/6.02         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('sup+', [status(thm)], ['178', '183'])).
% 5.84/6.02  thf('185', plain,
% 5.84/6.02      ((((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.84/6.02         | ~ (l1_struct_0 @ sk_A)))
% 5.84/6.02         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('sup+', [status(thm)], ['177', '184'])).
% 5.84/6.02  thf('186', plain, ((l1_struct_0 @ sk_A)),
% 5.84/6.02      inference('sup-', [status(thm)], ['14', '15'])).
% 5.84/6.02  thf('187', plain,
% 5.84/6.02      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 5.84/6.02         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('demod', [status(thm)], ['185', '186'])).
% 5.84/6.02  thf('188', plain,
% 5.84/6.02      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 5.84/6.02         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 5.84/6.02      inference('demod', [status(thm)], ['152', '153'])).
% 5.84/6.02  thf('189', plain,
% 5.84/6.02      (![X41 : $i, X42 : $i]:
% 5.84/6.02         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 5.84/6.02          | ~ (v3_pre_topc @ 
% 5.84/6.02               (k7_subset_1 @ (u1_struct_0 @ X42) @ (k2_struct_0 @ X42) @ X41) @ 
% 5.84/6.02               X42)
% 5.84/6.02          | (v4_pre_topc @ X41 @ X42)
% 5.84/6.02          | ~ (l1_pre_topc @ X42))),
% 5.84/6.02      inference('cnf', [status(esa)], [d6_pre_topc])).
% 5.84/6.02  thf('190', plain,
% 5.84/6.02      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.84/6.02        | ~ (l1_pre_topc @ sk_A)
% 5.84/6.02        | (v4_pre_topc @ sk_B @ sk_A)
% 5.84/6.02        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.84/6.02      inference('sup-', [status(thm)], ['188', '189'])).
% 5.84/6.02  thf('191', plain, ((l1_pre_topc @ sk_A)),
% 5.84/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.02  thf('192', plain,
% 5.84/6.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.84/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.84/6.02  thf('193', plain,
% 5.84/6.02      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 5.84/6.02        | (v4_pre_topc @ sk_B @ sk_A))),
% 5.84/6.02      inference('demod', [status(thm)], ['190', '191', '192'])).
% 5.84/6.02  thf('194', plain,
% 5.84/6.02      (((v4_pre_topc @ sk_B @ sk_A))
% 5.84/6.02         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 5.84/6.02      inference('sup-', [status(thm)], ['187', '193'])).
% 5.84/6.02  thf('195', plain,
% 5.84/6.02      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 5.84/6.02      inference('split', [status(esa)], ['0'])).
% 5.84/6.02  thf('196', plain,
% 5.84/6.02      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 5.84/6.02       ((v4_pre_topc @ sk_B @ sk_A))),
% 5.84/6.02      inference('sup-', [status(thm)], ['194', '195'])).
% 5.84/6.02  thf('197', plain, ($false),
% 5.84/6.02      inference('sat_resolution*', [status(thm)], ['1', '175', '176', '196'])).
% 5.84/6.02  
% 5.84/6.02  % SZS output end Refutation
% 5.84/6.02  
% 5.84/6.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
