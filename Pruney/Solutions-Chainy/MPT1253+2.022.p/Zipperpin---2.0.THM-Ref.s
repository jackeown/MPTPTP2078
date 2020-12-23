%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y5G3DKOLBl

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:15 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 267 expanded)
%              Number of leaves         :   32 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  636 (2055 expanded)
%              Number of equality atoms :   41 (  81 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X39: $i] :
      ( ( ( k2_struct_0 @ X39 )
        = ( u1_struct_0 @ X39 ) )
      | ~ ( l1_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('5',plain,(
    ! [X41: $i] :
      ( ( l1_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X39: $i] :
      ( ( ( k2_struct_0 @ X39 )
        = ( u1_struct_0 @ X39 ) )
      | ~ ( l1_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k2_tops_1 @ X45 @ X44 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k2_pre_topc @ X45 @ X44 ) @ ( k2_pre_topc @ X45 @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ X1 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ X1 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X39: $i] :
      ( ( ( k2_struct_0 @ X39 )
        = ( u1_struct_0 @ X39 ) )
      | ~ ( l1_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('28',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v4_pre_topc @ X42 @ X43 )
      | ( ( k2_pre_topc @ X43 @ X42 )
        = X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X13 @ X15 @ X14 )
        = ( k9_subset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k9_subset_1 @ X28 @ X26 @ X27 )
        = ( k3_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('49',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','26','35','36','39','46','47','48'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('50',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('51',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('55',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ ( k3_xboole_0 @ X5 @ X7 ) ) @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ ( k3_xboole_0 @ X2 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('57',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['49','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y5G3DKOLBl
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.80/1.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.02  % Solved by: fo/fo7.sh
% 0.80/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.02  % done 1140 iterations in 0.568s
% 0.80/1.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.02  % SZS output start Refutation
% 0.80/1.02  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.80/1.02  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.80/1.02  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.80/1.02  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.02  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.80/1.02  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.80/1.02  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.80/1.02  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.80/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.02  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.80/1.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.80/1.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.80/1.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.02  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.80/1.02  thf(t69_tops_1, conjecture,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_pre_topc @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( v4_pre_topc @ B @ A ) =>
% 0.80/1.02             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.80/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.02    (~( ![A:$i]:
% 0.80/1.02        ( ( l1_pre_topc @ A ) =>
% 0.80/1.02          ( ![B:$i]:
% 0.80/1.02            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02              ( ( v4_pre_topc @ B @ A ) =>
% 0.80/1.02                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 0.80/1.02    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 0.80/1.02  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(d3_struct_0, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.80/1.02  thf('1', plain,
% 0.80/1.02      (![X39 : $i]:
% 0.80/1.02         (((k2_struct_0 @ X39) = (u1_struct_0 @ X39)) | ~ (l1_struct_0 @ X39))),
% 0.80/1.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.80/1.02  thf('2', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('3', plain,
% 0.80/1.02      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.80/1.02        | ~ (l1_struct_0 @ sk_A))),
% 0.80/1.02      inference('sup+', [status(thm)], ['1', '2'])).
% 0.80/1.02  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf(dt_l1_pre_topc, axiom,
% 0.80/1.02    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.80/1.02  thf('5', plain, (![X41 : $i]: ((l1_struct_0 @ X41) | ~ (l1_pre_topc @ X41))),
% 0.80/1.02      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.80/1.02  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.80/1.02      inference('sup-', [status(thm)], ['4', '5'])).
% 0.80/1.02  thf('7', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.80/1.02      inference('demod', [status(thm)], ['3', '6'])).
% 0.80/1.02  thf('8', plain,
% 0.80/1.02      (![X39 : $i]:
% 0.80/1.02         (((k2_struct_0 @ X39) = (u1_struct_0 @ X39)) | ~ (l1_struct_0 @ X39))),
% 0.80/1.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.80/1.02  thf(d2_tops_1, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_pre_topc @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( k2_tops_1 @ A @ B ) =
% 0.80/1.02             ( k9_subset_1 @
% 0.80/1.02               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.80/1.02               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.80/1.02  thf('9', plain,
% 0.80/1.02      (![X44 : $i, X45 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.80/1.02          | ((k2_tops_1 @ X45 @ X44)
% 0.80/1.02              = (k9_subset_1 @ (u1_struct_0 @ X45) @ 
% 0.80/1.02                 (k2_pre_topc @ X45 @ X44) @ 
% 0.80/1.02                 (k2_pre_topc @ X45 @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44))))
% 0.80/1.02          | ~ (l1_pre_topc @ X45))),
% 0.80/1.02      inference('cnf', [status(esa)], [d2_tops_1])).
% 0.80/1.02  thf('10', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.80/1.02          | ~ (l1_struct_0 @ X0)
% 0.80/1.02          | ~ (l1_pre_topc @ X0)
% 0.80/1.02          | ((k2_tops_1 @ X0 @ X1)
% 0.80/1.02              = (k9_subset_1 @ (u1_struct_0 @ X0) @ (k2_pre_topc @ X0 @ X1) @ 
% 0.80/1.02                 (k2_pre_topc @ X0 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1)))))),
% 0.80/1.02      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.02  thf('11', plain,
% 0.80/1.02      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.02          = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.02             (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.02             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.80/1.02        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.02        | ~ (l1_struct_0 @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['7', '10'])).
% 0.80/1.02  thf('12', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.80/1.02      inference('demod', [status(thm)], ['3', '6'])).
% 0.80/1.02  thf(t3_subset, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.80/1.02  thf('13', plain,
% 0.80/1.02      (![X33 : $i, X34 : $i]:
% 0.80/1.02         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.80/1.02  thf('14', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['12', '13'])).
% 0.80/1.02  thf(t12_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.80/1.02  thf('15', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.80/1.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.80/1.02  thf('16', plain,
% 0.80/1.02      (((k2_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['14', '15'])).
% 0.80/1.02  thf('17', plain,
% 0.80/1.02      (![X39 : $i]:
% 0.80/1.02         (((k2_struct_0 @ X39) = (u1_struct_0 @ X39)) | ~ (l1_struct_0 @ X39))),
% 0.80/1.02      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.80/1.02  thf('18', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('19', plain,
% 0.80/1.02      (![X33 : $i, X34 : $i]:
% 0.80/1.02         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.80/1.02  thf('20', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['18', '19'])).
% 0.80/1.02  thf('21', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.80/1.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.80/1.02  thf('22', plain,
% 0.80/1.02      (((k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.02  thf('23', plain,
% 0.80/1.02      ((((k2_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.80/1.02        | ~ (l1_struct_0 @ sk_A))),
% 0.80/1.02      inference('sup+', [status(thm)], ['17', '22'])).
% 0.80/1.02  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.80/1.02      inference('sup-', [status(thm)], ['4', '5'])).
% 0.80/1.02  thf('25', plain,
% 0.80/1.02      (((k2_xboole_0 @ sk_B @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.80/1.02      inference('demod', [status(thm)], ['23', '24'])).
% 0.80/1.02  thf('26', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.80/1.02      inference('sup+', [status(thm)], ['16', '25'])).
% 0.80/1.02  thf('27', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.80/1.02      inference('demod', [status(thm)], ['3', '6'])).
% 0.80/1.02  thf('28', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.80/1.02      inference('sup+', [status(thm)], ['16', '25'])).
% 0.80/1.02  thf(t52_pre_topc, axiom,
% 0.80/1.02    (![A:$i]:
% 0.80/1.02     ( ( l1_pre_topc @ A ) =>
% 0.80/1.02       ( ![B:$i]:
% 0.80/1.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.02           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.80/1.02             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.80/1.02               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.80/1.02  thf('29', plain,
% 0.80/1.02      (![X42 : $i, X43 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.80/1.02          | ~ (v4_pre_topc @ X42 @ X43)
% 0.80/1.02          | ((k2_pre_topc @ X43 @ X42) = (X42))
% 0.80/1.02          | ~ (l1_pre_topc @ X43))),
% 0.80/1.02      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.80/1.02  thf('30', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.80/1.02          | ~ (l1_pre_topc @ sk_A)
% 0.80/1.02          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 0.80/1.02          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.80/1.02      inference('sup-', [status(thm)], ['28', '29'])).
% 0.80/1.02  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('32', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.80/1.02          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 0.80/1.02          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.80/1.02      inference('demod', [status(thm)], ['30', '31'])).
% 0.80/1.02  thf('33', plain,
% 0.80/1.02      ((~ (v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.80/1.02      inference('sup-', [status(thm)], ['27', '32'])).
% 0.80/1.02  thf('34', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('35', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.80/1.02      inference('demod', [status(thm)], ['33', '34'])).
% 0.80/1.02  thf('36', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.80/1.02      inference('sup+', [status(thm)], ['16', '25'])).
% 0.80/1.02  thf('37', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.80/1.02      inference('demod', [status(thm)], ['3', '6'])).
% 0.80/1.02  thf(d5_subset_1, axiom,
% 0.80/1.02    (![A:$i,B:$i]:
% 0.80/1.02     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.02       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.80/1.02  thf('38', plain,
% 0.80/1.02      (![X16 : $i, X17 : $i]:
% 0.80/1.02         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.80/1.02          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.80/1.02      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.80/1.02  thf('39', plain,
% 0.80/1.02      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.80/1.02         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.80/1.02      inference('sup-', [status(thm)], ['37', '38'])).
% 0.80/1.02  thf('40', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.80/1.02      inference('demod', [status(thm)], ['3', '6'])).
% 0.80/1.02  thf(commutativity_k9_subset_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.02       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.80/1.02  thf('41', plain,
% 0.80/1.02      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.80/1.02         (((k9_subset_1 @ X13 @ X15 @ X14) = (k9_subset_1 @ X13 @ X14 @ X15))
% 0.80/1.02          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.80/1.02      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.80/1.02  thf('42', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.80/1.02           = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['40', '41'])).
% 0.80/1.02  thf('43', plain,
% 0.80/1.02      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.80/1.02      inference('demod', [status(thm)], ['3', '6'])).
% 0.80/1.02  thf(redefinition_k9_subset_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.02       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.80/1.02  thf('44', plain,
% 0.80/1.02      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.80/1.02         (((k9_subset_1 @ X28 @ X26 @ X27) = (k3_xboole_0 @ X26 @ X27))
% 0.80/1.02          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.80/1.02      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.80/1.02  thf('45', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.80/1.02           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.80/1.02      inference('sup-', [status(thm)], ['43', '44'])).
% 0.80/1.02  thf('46', plain,
% 0.80/1.02      (![X0 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X0 @ sk_B)
% 0.80/1.02           = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.80/1.02      inference('demod', [status(thm)], ['42', '45'])).
% 0.80/1.02  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.02  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.80/1.02      inference('sup-', [status(thm)], ['4', '5'])).
% 0.80/1.02  thf('49', plain,
% 0.80/1.02      (((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.02         = (k3_xboole_0 @ 
% 0.80/1.02            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.80/1.02            sk_B))),
% 0.80/1.02      inference('demod', [status(thm)],
% 0.80/1.02                ['11', '26', '35', '36', '39', '46', '47', '48'])).
% 0.80/1.02  thf(t4_subset_1, axiom,
% 0.80/1.02    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.80/1.02  thf('50', plain,
% 0.80/1.02      (![X32 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 0.80/1.02      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.80/1.02  thf('51', plain,
% 0.80/1.02      (![X33 : $i, X34 : $i]:
% 0.80/1.02         ((r1_tarski @ X33 @ X34) | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t3_subset])).
% 0.80/1.02  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.80/1.02      inference('sup-', [status(thm)], ['50', '51'])).
% 0.80/1.02  thf('53', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.80/1.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.80/1.02  thf('54', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['52', '53'])).
% 0.80/1.02  thf(t31_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( r1_tarski @
% 0.80/1.02       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.80/1.02       ( k2_xboole_0 @ B @ C ) ))).
% 0.80/1.02  thf('55', plain,
% 0.80/1.02      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.80/1.02         (r1_tarski @ 
% 0.80/1.02          (k2_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ (k3_xboole_0 @ X5 @ X7)) @ 
% 0.80/1.02          (k2_xboole_0 @ X6 @ X7))),
% 0.80/1.02      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.80/1.02  thf(t23_xboole_1, axiom,
% 0.80/1.02    (![A:$i,B:$i,C:$i]:
% 0.80/1.02     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.80/1.02       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.80/1.02  thf('56', plain,
% 0.80/1.02      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.80/1.02         ((k3_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4))
% 0.80/1.02           = (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ (k3_xboole_0 @ X2 @ X4)))),
% 0.80/1.02      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.80/1.02  thf('57', plain,
% 0.80/1.02      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.80/1.02         (r1_tarski @ (k3_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X7)) @ 
% 0.80/1.02          (k2_xboole_0 @ X6 @ X7))),
% 0.80/1.02      inference('demod', [status(thm)], ['55', '56'])).
% 0.80/1.02  thf('58', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]:
% 0.80/1.02         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.80/1.02          (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.80/1.02      inference('sup+', [status(thm)], ['54', '57'])).
% 0.80/1.02  thf('59', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.80/1.02      inference('sup-', [status(thm)], ['52', '53'])).
% 0.80/1.02  thf('60', plain,
% 0.80/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.80/1.02      inference('demod', [status(thm)], ['58', '59'])).
% 0.80/1.02  thf('61', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.80/1.02      inference('sup+', [status(thm)], ['49', '60'])).
% 0.80/1.02  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.80/1.02  
% 0.80/1.02  % SZS output end Refutation
% 0.80/1.02  
% 0.80/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
