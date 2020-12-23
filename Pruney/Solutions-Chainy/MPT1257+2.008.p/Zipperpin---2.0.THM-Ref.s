%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j80jBEHruS

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:18 EST 2020

% Result     : Theorem 54.42s
% Output     : Refutation 54.42s
% Verified   : 
% Statistics : Number of formulae       :  236 (2805 expanded)
%              Number of leaves         :   34 ( 854 expanded)
%              Depth                    :   24
%              Number of atoms          : 2439 (26878 expanded)
%              Number of equality atoms :   90 ( 988 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(t73_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_tops_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l1_pre_topc @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X46 @ X47 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_pre_topc @ X51 @ X50 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 @ ( k2_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( ( k2_tops_1 @ X49 @ X48 )
        = ( k2_tops_1 @ X49 @ ( k3_subset_1 @ ( u1_struct_0 @ X49 ) @ X48 ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('28',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('30',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','30'])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('33',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( ( k1_tops_1 @ X43 @ X42 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X43 ) @ ( k2_pre_topc @ X43 @ ( k3_subset_1 @ ( u1_struct_0 @ X43 ) @ X42 ) ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('39',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('42',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('45',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k2_pre_topc @ X51 @ X50 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 @ ( k2_tops_1 @ X51 @ X50 ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','56'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('58',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X34 @ X35 ) @ ( k3_subset_1 @ X34 @ ( k9_subset_1 @ X34 @ X35 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('63',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('65',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('77',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X23 @ X21 )
        = ( k9_subset_1 @ X22 @ X23 @ ( k3_subset_1 @ X22 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = ( k9_subset_1 @ X0 @ X1 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('80',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('88',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X19 @ X18 ) @ ( k3_subset_1 @ X19 @ X20 ) )
      | ( r1_tarski @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('94',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('95',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['92','93','96'])).

thf('98',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('101',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('105',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('106',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('109',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ( r1_tarski @ ( k3_subset_1 @ X19 @ X18 ) @ ( k3_subset_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_B ) @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['107','114'])).

thf('116',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('117',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('118',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
    = ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('120',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['115','120'])).

thf('122',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('123',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    | ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('125',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('126',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_xboole_0 @ X38 @ X36 )
      | ( r1_tarski @ X38 @ ( k3_subset_1 @ X37 @ X36 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('133',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('135',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('137',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['133','134','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X38 @ ( k3_subset_1 @ X37 @ X36 ) )
      | ( r1_xboole_0 @ X38 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ sk_B )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( r1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['138','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('146',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['130','146'])).

thf('148',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['123','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('150',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('153',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('154',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','155'])).

thf('157',plain,
    ( sk_B
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','148','151','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('159',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X10 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('164',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['162','165'])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('167',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k2_tops_1 @ X45 @ X44 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X45 ) @ ( k2_pre_topc @ X45 @ X44 ) @ ( k2_pre_topc @ X45 @ ( k3_subset_1 @ ( u1_struct_0 @ X45 ) @ X44 ) ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X0 ) ) ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('170',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) )
      = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X0 ) ) ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( k2_pre_topc @ X0 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['168','173'])).

thf('175',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['157','174'])).

thf('176',plain,
    ( sk_B
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','148','151','156'])).

thf('177',plain,
    ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('178',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('179',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','30'])).

thf('180',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('181',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('183',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['178','183'])).

thf('185',plain,
    ( sk_B
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','148','151','156'])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['175','176','177','184','185','186'])).

thf('188',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('189',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('190',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','65','187','190'])).

thf('192',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('193',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( r1_tarski @ X38 @ ( k3_subset_1 @ X37 @ X36 ) )
      | ( r1_xboole_0 @ X38 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['191','196'])).

thf('198',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('199',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    $false ),
    inference(demod,[status(thm)],['0','199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j80jBEHruS
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:38:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 54.42/54.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 54.42/54.60  % Solved by: fo/fo7.sh
% 54.42/54.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.42/54.60  % done 18544 iterations in 54.113s
% 54.42/54.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 54.42/54.60  % SZS output start Refutation
% 54.42/54.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 54.42/54.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 54.42/54.60  thf(sk_A_type, type, sk_A: $i).
% 54.42/54.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 54.42/54.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 54.42/54.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 54.42/54.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 54.42/54.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 54.42/54.60  thf(sk_B_type, type, sk_B: $i).
% 54.42/54.60  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 54.42/54.60  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 54.42/54.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 54.42/54.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 54.42/54.60  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 54.42/54.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 54.42/54.60  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 54.42/54.60  thf(t73_tops_1, conjecture,
% 54.42/54.60    (![A:$i]:
% 54.42/54.60     ( ( l1_pre_topc @ A ) =>
% 54.42/54.60       ( ![B:$i]:
% 54.42/54.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.42/54.60           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 54.42/54.60  thf(zf_stmt_0, negated_conjecture,
% 54.42/54.60    (~( ![A:$i]:
% 54.42/54.60        ( ( l1_pre_topc @ A ) =>
% 54.42/54.60          ( ![B:$i]:
% 54.42/54.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.42/54.60              ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ) )),
% 54.42/54.60    inference('cnf.neg', [status(esa)], [t73_tops_1])).
% 54.42/54.60  thf('0', plain,
% 54.42/54.60      (~ (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('1', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf(dt_k2_tops_1, axiom,
% 54.42/54.60    (![A:$i,B:$i]:
% 54.42/54.60     ( ( ( l1_pre_topc @ A ) & 
% 54.42/54.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 54.42/54.60       ( m1_subset_1 @
% 54.42/54.60         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 54.42/54.60  thf('2', plain,
% 54.42/54.60      (![X46 : $i, X47 : $i]:
% 54.42/54.60         (~ (l1_pre_topc @ X46)
% 54.42/54.60          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 54.42/54.60          | (m1_subset_1 @ (k2_tops_1 @ X46 @ X47) @ 
% 54.42/54.60             (k1_zfmisc_1 @ (u1_struct_0 @ X46))))),
% 54.42/54.60      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 54.42/54.60  thf('3', plain,
% 54.42/54.60      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.42/54.60        | ~ (l1_pre_topc @ sk_A))),
% 54.42/54.60      inference('sup-', [status(thm)], ['1', '2'])).
% 54.42/54.60  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('5', plain,
% 54.42/54.60      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['3', '4'])).
% 54.42/54.60  thf('6', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf(dt_k3_subset_1, axiom,
% 54.42/54.60    (![A:$i,B:$i]:
% 54.42/54.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 54.42/54.60  thf('7', plain,
% 54.42/54.60      (![X5 : $i, X6 : $i]:
% 54.42/54.60         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 54.42/54.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 54.42/54.60      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 54.42/54.60  thf('8', plain,
% 54.42/54.60      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['6', '7'])).
% 54.42/54.60  thf('9', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf(d5_subset_1, axiom,
% 54.42/54.60    (![A:$i,B:$i]:
% 54.42/54.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 54.42/54.60  thf('10', plain,
% 54.42/54.60      (![X3 : $i, X4 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 54.42/54.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 54.42/54.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 54.42/54.60  thf('11', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['9', '10'])).
% 54.42/54.60  thf('12', plain,
% 54.42/54.60      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['8', '11'])).
% 54.42/54.60  thf(dt_k4_subset_1, axiom,
% 54.42/54.60    (![A:$i,B:$i,C:$i]:
% 54.42/54.60     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 54.42/54.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 54.42/54.60       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 54.42/54.60  thf('13', plain,
% 54.42/54.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 54.42/54.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 54.42/54.60          | (m1_subset_1 @ (k4_subset_1 @ X8 @ X7 @ X9) @ (k1_zfmisc_1 @ X8)))),
% 54.42/54.60      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 54.42/54.60  thf('14', plain,
% 54.42/54.60      (![X0 : $i]:
% 54.42/54.60         ((m1_subset_1 @ 
% 54.42/54.60           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0) @ 
% 54.42/54.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.42/54.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['12', '13'])).
% 54.42/54.60  thf('15', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60         (k2_tops_1 @ sk_A @ sk_B)) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['5', '14'])).
% 54.42/54.60  thf('16', plain,
% 54.42/54.60      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['8', '11'])).
% 54.42/54.60  thf(t65_tops_1, axiom,
% 54.42/54.60    (![A:$i]:
% 54.42/54.60     ( ( l1_pre_topc @ A ) =>
% 54.42/54.60       ( ![B:$i]:
% 54.42/54.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.42/54.60           ( ( k2_pre_topc @ A @ B ) =
% 54.42/54.60             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 54.42/54.60  thf('17', plain,
% 54.42/54.60      (![X50 : $i, X51 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 54.42/54.60          | ((k2_pre_topc @ X51 @ X50)
% 54.42/54.60              = (k4_subset_1 @ (u1_struct_0 @ X51) @ X50 @ 
% 54.42/54.60                 (k2_tops_1 @ X51 @ X50)))
% 54.42/54.60          | ~ (l1_pre_topc @ X51))),
% 54.42/54.60      inference('cnf', [status(esa)], [t65_tops_1])).
% 54.42/54.60  thf('18', plain,
% 54.42/54.60      ((~ (l1_pre_topc @ sk_A)
% 54.42/54.60        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 54.42/54.60            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60               (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60               (k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['16', '17'])).
% 54.42/54.60  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('20', plain,
% 54.42/54.60      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['8', '11'])).
% 54.42/54.60  thf(t62_tops_1, axiom,
% 54.42/54.60    (![A:$i]:
% 54.42/54.60     ( ( l1_pre_topc @ A ) =>
% 54.42/54.60       ( ![B:$i]:
% 54.42/54.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.42/54.60           ( ( k2_tops_1 @ A @ B ) =
% 54.42/54.60             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 54.42/54.60  thf('21', plain,
% 54.42/54.60      (![X48 : $i, X49 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 54.42/54.60          | ((k2_tops_1 @ X49 @ X48)
% 54.42/54.60              = (k2_tops_1 @ X49 @ (k3_subset_1 @ (u1_struct_0 @ X49) @ X48)))
% 54.42/54.60          | ~ (l1_pre_topc @ X49))),
% 54.42/54.60      inference('cnf', [status(esa)], [t62_tops_1])).
% 54.42/54.60  thf('22', plain,
% 54.42/54.60      ((~ (l1_pre_topc @ sk_A)
% 54.42/54.60        | ((k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 54.42/54.60            = (k2_tops_1 @ sk_A @ 
% 54.42/54.60               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60                (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['20', '21'])).
% 54.42/54.60  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('24', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf(involutiveness_k3_subset_1, axiom,
% 54.42/54.60    (![A:$i,B:$i]:
% 54.42/54.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 54.42/54.60  thf('25', plain,
% 54.42/54.60      (![X13 : $i, X14 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 54.42/54.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 54.42/54.60      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 54.42/54.60  thf('26', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['24', '25'])).
% 54.42/54.60  thf('27', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['9', '10'])).
% 54.42/54.60  thf('28', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 54.42/54.60      inference('demod', [status(thm)], ['26', '27'])).
% 54.42/54.60  thf('29', plain,
% 54.42/54.60      (((k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 54.42/54.60         = (k2_tops_1 @ sk_A @ sk_B))),
% 54.42/54.60      inference('demod', [status(thm)], ['22', '23', '28'])).
% 54.42/54.60  thf('30', plain,
% 54.42/54.60      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 54.42/54.60         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60            (k2_tops_1 @ sk_A @ sk_B)))),
% 54.42/54.60      inference('demod', [status(thm)], ['18', '19', '29'])).
% 54.42/54.60  thf('31', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['15', '30'])).
% 54.42/54.60  thf('32', plain,
% 54.42/54.60      (![X5 : $i, X6 : $i]:
% 54.42/54.60         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 54.42/54.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 54.42/54.60      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 54.42/54.60  thf('33', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['31', '32'])).
% 54.42/54.60  thf('34', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf(d1_tops_1, axiom,
% 54.42/54.60    (![A:$i]:
% 54.42/54.60     ( ( l1_pre_topc @ A ) =>
% 54.42/54.60       ( ![B:$i]:
% 54.42/54.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.42/54.60           ( ( k1_tops_1 @ A @ B ) =
% 54.42/54.60             ( k3_subset_1 @
% 54.42/54.60               ( u1_struct_0 @ A ) @ 
% 54.42/54.60               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 54.42/54.60  thf('35', plain,
% 54.42/54.60      (![X42 : $i, X43 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 54.42/54.60          | ((k1_tops_1 @ X43 @ X42)
% 54.42/54.60              = (k3_subset_1 @ (u1_struct_0 @ X43) @ 
% 54.42/54.60                 (k2_pre_topc @ X43 @ (k3_subset_1 @ (u1_struct_0 @ X43) @ X42))))
% 54.42/54.60          | ~ (l1_pre_topc @ X43))),
% 54.42/54.60      inference('cnf', [status(esa)], [d1_tops_1])).
% 54.42/54.60  thf('36', plain,
% 54.42/54.60      ((~ (l1_pre_topc @ sk_A)
% 54.42/54.60        | ((k1_tops_1 @ sk_A @ sk_B)
% 54.42/54.60            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60               (k2_pre_topc @ sk_A @ 
% 54.42/54.60                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['34', '35'])).
% 54.42/54.60  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('38', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['9', '10'])).
% 54.42/54.60  thf('39', plain,
% 54.42/54.60      (((k1_tops_1 @ sk_A @ sk_B)
% 54.42/54.60         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 54.42/54.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 54.42/54.60  thf('40', plain,
% 54.42/54.60      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['33', '39'])).
% 54.42/54.60  thf('41', plain,
% 54.42/54.60      (![X5 : $i, X6 : $i]:
% 54.42/54.60         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 54.42/54.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 54.42/54.60      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 54.42/54.60  thf('42', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['40', '41'])).
% 54.42/54.60  thf('43', plain,
% 54.42/54.60      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['33', '39'])).
% 54.42/54.60  thf('44', plain,
% 54.42/54.60      (![X3 : $i, X4 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 54.42/54.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 54.42/54.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 54.42/54.60  thf('45', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['43', '44'])).
% 54.42/54.60  thf('46', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['42', '45'])).
% 54.42/54.60  thf('47', plain,
% 54.42/54.60      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['3', '4'])).
% 54.42/54.60  thf('48', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('49', plain,
% 54.42/54.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 54.42/54.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 54.42/54.60          | (m1_subset_1 @ (k4_subset_1 @ X8 @ X7 @ X9) @ (k1_zfmisc_1 @ X8)))),
% 54.42/54.60      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 54.42/54.60  thf('50', plain,
% 54.42/54.60      (![X0 : $i]:
% 54.42/54.60         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 54.42/54.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.42/54.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['48', '49'])).
% 54.42/54.60  thf('51', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['47', '50'])).
% 54.42/54.60  thf('52', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('53', plain,
% 54.42/54.60      (![X50 : $i, X51 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 54.42/54.60          | ((k2_pre_topc @ X51 @ X50)
% 54.42/54.60              = (k4_subset_1 @ (u1_struct_0 @ X51) @ X50 @ 
% 54.42/54.60                 (k2_tops_1 @ X51 @ X50)))
% 54.42/54.60          | ~ (l1_pre_topc @ X51))),
% 54.42/54.60      inference('cnf', [status(esa)], [t65_tops_1])).
% 54.42/54.60  thf('54', plain,
% 54.42/54.60      ((~ (l1_pre_topc @ sk_A)
% 54.42/54.60        | ((k2_pre_topc @ sk_A @ sk_B)
% 54.42/54.60            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 54.42/54.60               (k2_tops_1 @ sk_A @ sk_B))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['52', '53'])).
% 54.42/54.60  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('56', plain,
% 54.42/54.60      (((k2_pre_topc @ sk_A @ sk_B)
% 54.42/54.60         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 54.42/54.60            (k2_tops_1 @ sk_A @ sk_B)))),
% 54.42/54.60      inference('demod', [status(thm)], ['54', '55'])).
% 54.42/54.60  thf('57', plain,
% 54.42/54.60      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['51', '56'])).
% 54.42/54.60  thf(t42_subset_1, axiom,
% 54.42/54.60    (![A:$i,B:$i]:
% 54.42/54.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60       ( ![C:$i]:
% 54.42/54.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60           ( r1_tarski @
% 54.42/54.60             ( k3_subset_1 @ A @ B ) @ 
% 54.42/54.60             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 54.42/54.60  thf('58', plain,
% 54.42/54.60      (![X33 : $i, X34 : $i, X35 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 54.42/54.60          | (r1_tarski @ (k3_subset_1 @ X34 @ X35) @ 
% 54.42/54.60             (k3_subset_1 @ X34 @ (k9_subset_1 @ X34 @ X35 @ X33)))
% 54.42/54.60          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 54.42/54.60      inference('cnf', [status(esa)], [t42_subset_1])).
% 54.42/54.60  thf('59', plain,
% 54.42/54.60      (![X0 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.42/54.60          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 54.42/54.60             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 54.42/54.60               (k2_pre_topc @ sk_A @ sk_B)))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['57', '58'])).
% 54.42/54.60  thf('60', plain,
% 54.42/54.60      ((r1_tarski @ 
% 54.42/54.60        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 54.42/54.60        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 54.42/54.60          (k2_pre_topc @ sk_A @ sk_B))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['46', '59'])).
% 54.42/54.60  thf('61', plain,
% 54.42/54.60      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['33', '39'])).
% 54.42/54.60  thf('62', plain,
% 54.42/54.60      (![X13 : $i, X14 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 54.42/54.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 54.42/54.60      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 54.42/54.60  thf('63', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 54.42/54.60         = (k1_tops_1 @ sk_A @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['61', '62'])).
% 54.42/54.60  thf('64', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['43', '44'])).
% 54.42/54.60  thf('65', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 54.42/54.60         = (k1_tops_1 @ sk_A @ sk_B))),
% 54.42/54.60      inference('demod', [status(thm)], ['63', '64'])).
% 54.42/54.60  thf('66', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf(d10_xboole_0, axiom,
% 54.42/54.60    (![A:$i,B:$i]:
% 54.42/54.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 54.42/54.60  thf('67', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 54.42/54.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 54.42/54.60  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 54.42/54.60      inference('simplify', [status(thm)], ['67'])).
% 54.42/54.60  thf(t3_subset, axiom,
% 54.42/54.60    (![A:$i,B:$i]:
% 54.42/54.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 54.42/54.60  thf('69', plain,
% 54.42/54.60      (![X39 : $i, X41 : $i]:
% 54.42/54.60         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 54.42/54.60      inference('cnf', [status(esa)], [t3_subset])).
% 54.42/54.60  thf('70', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['68', '69'])).
% 54.42/54.60  thf('71', plain,
% 54.42/54.60      (![X5 : $i, X6 : $i]:
% 54.42/54.60         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 54.42/54.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 54.42/54.60      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 54.42/54.60  thf('72', plain,
% 54.42/54.60      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['70', '71'])).
% 54.42/54.60  thf('73', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['68', '69'])).
% 54.42/54.60  thf('74', plain,
% 54.42/54.60      (![X3 : $i, X4 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 54.42/54.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 54.42/54.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 54.42/54.60  thf('75', plain,
% 54.42/54.60      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['73', '74'])).
% 54.42/54.60  thf('76', plain,
% 54.42/54.60      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['72', '75'])).
% 54.42/54.60  thf(t32_subset_1, axiom,
% 54.42/54.60    (![A:$i,B:$i]:
% 54.42/54.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60       ( ![C:$i]:
% 54.42/54.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60           ( ( k7_subset_1 @ A @ B @ C ) =
% 54.42/54.60             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 54.42/54.60  thf('77', plain,
% 54.42/54.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 54.42/54.60          | ((k7_subset_1 @ X22 @ X23 @ X21)
% 54.42/54.60              = (k9_subset_1 @ X22 @ X23 @ (k3_subset_1 @ X22 @ X21)))
% 54.42/54.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 54.42/54.60      inference('cnf', [status(esa)], [t32_subset_1])).
% 54.42/54.60  thf('78', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 54.42/54.60          | ((k7_subset_1 @ X0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 54.42/54.60              = (k9_subset_1 @ X0 @ X1 @ 
% 54.42/54.60                 (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['76', '77'])).
% 54.42/54.60  thf('79', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['68', '69'])).
% 54.42/54.60  thf('80', plain,
% 54.42/54.60      (![X13 : $i, X14 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 54.42/54.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 54.42/54.60      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 54.42/54.60  thf('81', plain,
% 54.42/54.60      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['79', '80'])).
% 54.42/54.60  thf('82', plain,
% 54.42/54.60      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['73', '74'])).
% 54.42/54.60  thf('83', plain,
% 54.42/54.60      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['81', '82'])).
% 54.42/54.60  thf('84', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 54.42/54.60          | ((k7_subset_1 @ X0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 54.42/54.60              = (k9_subset_1 @ X0 @ X1 @ X0)))),
% 54.42/54.60      inference('demod', [status(thm)], ['78', '83'])).
% 54.42/54.60  thf('85', plain,
% 54.42/54.60      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 54.42/54.60         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['66', '84'])).
% 54.42/54.60  thf('86', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('87', plain,
% 54.42/54.60      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['81', '82'])).
% 54.42/54.60  thf(t31_subset_1, axiom,
% 54.42/54.60    (![A:$i,B:$i]:
% 54.42/54.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60       ( ![C:$i]:
% 54.42/54.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60           ( ( r1_tarski @ B @ C ) <=>
% 54.42/54.60             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 54.42/54.60  thf('88', plain,
% 54.42/54.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 54.42/54.60          | ~ (r1_tarski @ (k3_subset_1 @ X19 @ X18) @ 
% 54.42/54.60               (k3_subset_1 @ X19 @ X20))
% 54.42/54.60          | (r1_tarski @ X20 @ X18)
% 54.42/54.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 54.42/54.60      inference('cnf', [status(esa)], [t31_subset_1])).
% 54.42/54.60  thf('89', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 54.42/54.60          | ~ (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))
% 54.42/54.60          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 54.42/54.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['87', '88'])).
% 54.42/54.60  thf('90', plain,
% 54.42/54.60      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['72', '75'])).
% 54.42/54.60  thf('91', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 54.42/54.60          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 54.42/54.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 54.42/54.60      inference('demod', [status(thm)], ['89', '90'])).
% 54.42/54.60  thf('92', plain,
% 54.42/54.60      (((r1_tarski @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B)
% 54.42/54.60        | ~ (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60             (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['86', '91'])).
% 54.42/54.60  thf('93', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['9', '10'])).
% 54.42/54.60  thf('94', plain,
% 54.42/54.60      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['8', '11'])).
% 54.42/54.60  thf('95', plain,
% 54.42/54.60      (![X39 : $i, X40 : $i]:
% 54.42/54.60         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 54.42/54.60      inference('cnf', [status(esa)], [t3_subset])).
% 54.42/54.60  thf('96', plain,
% 54.42/54.60      ((r1_tarski @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60        (u1_struct_0 @ sk_A))),
% 54.42/54.60      inference('sup-', [status(thm)], ['94', '95'])).
% 54.42/54.60  thf('97', plain,
% 54.42/54.60      ((r1_tarski @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B)),
% 54.42/54.60      inference('demod', [status(thm)], ['92', '93', '96'])).
% 54.42/54.60  thf('98', plain,
% 54.42/54.60      (![X39 : $i, X41 : $i]:
% 54.42/54.60         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 54.42/54.60      inference('cnf', [status(esa)], [t3_subset])).
% 54.42/54.60  thf('99', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 54.42/54.60        (k1_zfmisc_1 @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['97', '98'])).
% 54.42/54.60  thf('100', plain,
% 54.42/54.60      (![X5 : $i, X6 : $i]:
% 54.42/54.60         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 54.42/54.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 54.42/54.60      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 54.42/54.60  thf('101', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k3_subset_1 @ sk_B @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 54.42/54.60        (k1_zfmisc_1 @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['99', '100'])).
% 54.42/54.60  thf('102', plain,
% 54.42/54.60      (![X39 : $i, X40 : $i]:
% 54.42/54.60         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 54.42/54.60      inference('cnf', [status(esa)], [t3_subset])).
% 54.42/54.60  thf('103', plain,
% 54.42/54.60      ((r1_tarski @ 
% 54.42/54.60        (k3_subset_1 @ sk_B @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 54.42/54.60        sk_B)),
% 54.42/54.60      inference('sup-', [status(thm)], ['101', '102'])).
% 54.42/54.60  thf('104', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 54.42/54.60        (k1_zfmisc_1 @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['97', '98'])).
% 54.42/54.60  thf('105', plain,
% 54.42/54.60      (![X3 : $i, X4 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 54.42/54.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 54.42/54.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 54.42/54.60  thf('106', plain,
% 54.42/54.60      (((k3_subset_1 @ sk_B @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 54.42/54.60         = (k4_xboole_0 @ sk_B @ 
% 54.42/54.60            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['104', '105'])).
% 54.42/54.60  thf('107', plain,
% 54.42/54.60      ((r1_tarski @ 
% 54.42/54.60        (k4_xboole_0 @ sk_B @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))) @ 
% 54.42/54.60        sk_B)),
% 54.42/54.60      inference('demod', [status(thm)], ['103', '106'])).
% 54.42/54.60  thf('108', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['68', '69'])).
% 54.42/54.60  thf('109', plain,
% 54.42/54.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 54.42/54.60          | ~ (r1_tarski @ X20 @ X18)
% 54.42/54.60          | (r1_tarski @ (k3_subset_1 @ X19 @ X18) @ (k3_subset_1 @ X19 @ X20))
% 54.42/54.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 54.42/54.60      inference('cnf', [status(esa)], [t31_subset_1])).
% 54.42/54.60  thf('110', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 54.42/54.60          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 54.42/54.60          | ~ (r1_tarski @ X1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['108', '109'])).
% 54.42/54.60  thf('111', plain,
% 54.42/54.60      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['73', '74'])).
% 54.42/54.60  thf('112', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 54.42/54.60          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1))
% 54.42/54.60          | ~ (r1_tarski @ X1 @ X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['110', '111'])).
% 54.42/54.60  thf('113', plain,
% 54.42/54.60      (![X39 : $i, X41 : $i]:
% 54.42/54.60         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 54.42/54.60      inference('cnf', [status(esa)], [t3_subset])).
% 54.42/54.60  thf('114', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (r1_tarski @ X1 @ X0)
% 54.42/54.60          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ (k3_subset_1 @ X0 @ X1)))),
% 54.42/54.60      inference('clc', [status(thm)], ['112', '113'])).
% 54.42/54.60  thf('115', plain,
% 54.42/54.60      ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_B) @ 
% 54.42/54.60        (k3_subset_1 @ sk_B @ 
% 54.42/54.60         (k4_xboole_0 @ sk_B @ 
% 54.42/54.60          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['107', '114'])).
% 54.42/54.60  thf('116', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 54.42/54.60        (k1_zfmisc_1 @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['97', '98'])).
% 54.42/54.60  thf('117', plain,
% 54.42/54.60      (![X13 : $i, X14 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 54.42/54.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 54.42/54.60      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 54.42/54.60  thf('118', plain,
% 54.42/54.60      (((k3_subset_1 @ sk_B @ 
% 54.42/54.60         (k3_subset_1 @ sk_B @ 
% 54.42/54.60          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['116', '117'])).
% 54.42/54.60  thf('119', plain,
% 54.42/54.60      (((k3_subset_1 @ sk_B @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 54.42/54.60         = (k4_xboole_0 @ sk_B @ 
% 54.42/54.60            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['104', '105'])).
% 54.42/54.60  thf('120', plain,
% 54.42/54.60      (((k3_subset_1 @ sk_B @ 
% 54.42/54.60         (k4_xboole_0 @ sk_B @ 
% 54.42/54.60          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['118', '119'])).
% 54.42/54.60  thf('121', plain,
% 54.42/54.60      ((r1_tarski @ (k4_xboole_0 @ sk_B @ sk_B) @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['115', '120'])).
% 54.42/54.60  thf('122', plain,
% 54.42/54.60      (![X0 : $i, X2 : $i]:
% 54.42/54.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 54.42/54.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 54.42/54.60  thf('123', plain,
% 54.42/54.60      ((~ (r1_tarski @ 
% 54.42/54.60           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 54.42/54.60           (k4_xboole_0 @ sk_B @ sk_B))
% 54.42/54.60        | ((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 54.42/54.60            = (k4_xboole_0 @ sk_B @ sk_B)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['121', '122'])).
% 54.42/54.60  thf('124', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 54.42/54.60        (k1_zfmisc_1 @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['97', '98'])).
% 54.42/54.60  thf('125', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['68', '69'])).
% 54.42/54.60  thf(t43_subset_1, axiom,
% 54.42/54.60    (![A:$i,B:$i]:
% 54.42/54.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60       ( ![C:$i]:
% 54.42/54.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60           ( ( r1_xboole_0 @ B @ C ) <=>
% 54.42/54.60             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 54.42/54.60  thf('126', plain,
% 54.42/54.60      (![X36 : $i, X37 : $i, X38 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 54.42/54.60          | ~ (r1_xboole_0 @ X38 @ X36)
% 54.42/54.60          | (r1_tarski @ X38 @ (k3_subset_1 @ X37 @ X36))
% 54.42/54.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 54.42/54.60      inference('cnf', [status(esa)], [t43_subset_1])).
% 54.42/54.60  thf('127', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 54.42/54.60          | (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ X0))
% 54.42/54.60          | ~ (r1_xboole_0 @ X1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['125', '126'])).
% 54.42/54.60  thf('128', plain,
% 54.42/54.60      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['73', '74'])).
% 54.42/54.60  thf('129', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 54.42/54.60          | (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 54.42/54.60          | ~ (r1_xboole_0 @ X1 @ X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['127', '128'])).
% 54.42/54.60  thf('130', plain,
% 54.42/54.60      ((~ (r1_xboole_0 @ 
% 54.42/54.60           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B)
% 54.42/54.60        | (r1_tarski @ 
% 54.42/54.60           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 54.42/54.60           (k4_xboole_0 @ sk_B @ sk_B)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['124', '129'])).
% 54.42/54.60  thf('131', plain,
% 54.42/54.60      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['8', '11'])).
% 54.42/54.60  thf('132', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 54.42/54.60          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 54.42/54.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 54.42/54.60      inference('demod', [status(thm)], ['89', '90'])).
% 54.42/54.60  thf('133', plain,
% 54.42/54.60      (((r1_tarski @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 54.42/54.60        | ~ (r1_tarski @ 
% 54.42/54.60             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 54.42/54.60             (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['131', '132'])).
% 54.42/54.60  thf('134', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 54.42/54.60      inference('demod', [status(thm)], ['26', '27'])).
% 54.42/54.60  thf('135', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('136', plain,
% 54.42/54.60      (![X39 : $i, X40 : $i]:
% 54.42/54.60         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 54.42/54.60      inference('cnf', [status(esa)], [t3_subset])).
% 54.42/54.60  thf('137', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 54.42/54.60      inference('sup-', [status(thm)], ['135', '136'])).
% 54.42/54.60  thf('138', plain,
% 54.42/54.60      ((r1_tarski @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 54.42/54.60      inference('demod', [status(thm)], ['133', '134', '137'])).
% 54.42/54.60  thf('139', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('140', plain,
% 54.42/54.60      (![X36 : $i, X37 : $i, X38 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 54.42/54.60          | ~ (r1_tarski @ X38 @ (k3_subset_1 @ X37 @ X36))
% 54.42/54.60          | (r1_xboole_0 @ X38 @ X36)
% 54.42/54.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 54.42/54.60      inference('cnf', [status(esa)], [t43_subset_1])).
% 54.42/54.60  thf('141', plain,
% 54.42/54.60      (![X0 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.42/54.60          | (r1_xboole_0 @ X0 @ sk_B)
% 54.42/54.60          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['139', '140'])).
% 54.42/54.60  thf('142', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 54.42/54.60      inference('sup-', [status(thm)], ['9', '10'])).
% 54.42/54.60  thf('143', plain,
% 54.42/54.60      (![X0 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.42/54.60          | (r1_xboole_0 @ X0 @ sk_B)
% 54.42/54.60          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 54.42/54.60      inference('demod', [status(thm)], ['141', '142'])).
% 54.42/54.60  thf('144', plain,
% 54.42/54.60      (((r1_xboole_0 @ 
% 54.42/54.60         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B)
% 54.42/54.60        | ~ (m1_subset_1 @ 
% 54.42/54.60             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 54.42/54.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['138', '143'])).
% 54.42/54.60  thf('145', plain,
% 54.42/54.60      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['72', '75'])).
% 54.42/54.60  thf('146', plain,
% 54.42/54.60      ((r1_xboole_0 @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B)),
% 54.42/54.60      inference('demod', [status(thm)], ['144', '145'])).
% 54.42/54.60  thf('147', plain,
% 54.42/54.60      ((r1_tarski @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ 
% 54.42/54.60        (k4_xboole_0 @ sk_B @ sk_B))),
% 54.42/54.60      inference('demod', [status(thm)], ['130', '146'])).
% 54.42/54.60  thf('148', plain,
% 54.42/54.60      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 54.42/54.60         = (k4_xboole_0 @ sk_B @ sk_B))),
% 54.42/54.60      inference('demod', [status(thm)], ['123', '147'])).
% 54.42/54.60  thf('149', plain,
% 54.42/54.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf(redefinition_k7_subset_1, axiom,
% 54.42/54.60    (![A:$i,B:$i,C:$i]:
% 54.42/54.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 54.42/54.60  thf('150', plain,
% 54.42/54.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 54.42/54.60          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 54.42/54.60      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 54.42/54.60  thf('151', plain,
% 54.42/54.60      (![X0 : $i]:
% 54.42/54.60         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 54.42/54.60           = (k4_xboole_0 @ sk_B @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['149', '150'])).
% 54.42/54.60  thf('152', plain,
% 54.42/54.60      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['81', '82'])).
% 54.42/54.60  thf('153', plain,
% 54.42/54.60      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['72', '75'])).
% 54.42/54.60  thf('154', plain,
% 54.42/54.60      (![X3 : $i, X4 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 54.42/54.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 54.42/54.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 54.42/54.60  thf('155', plain,
% 54.42/54.60      (![X0 : $i]:
% 54.42/54.60         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 54.42/54.60           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['153', '154'])).
% 54.42/54.60  thf('156', plain,
% 54.42/54.60      (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 54.42/54.60      inference('sup+', [status(thm)], ['152', '155'])).
% 54.42/54.60  thf('157', plain,
% 54.42/54.60      (((sk_B)
% 54.42/54.60         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['85', '148', '151', '156'])).
% 54.42/54.60  thf('158', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['68', '69'])).
% 54.42/54.60  thf(dt_k9_subset_1, axiom,
% 54.42/54.60    (![A:$i,B:$i,C:$i]:
% 54.42/54.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 54.42/54.60       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 54.42/54.60  thf('159', plain,
% 54.42/54.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 54.42/54.60         ((m1_subset_1 @ (k9_subset_1 @ X10 @ X11 @ X12) @ (k1_zfmisc_1 @ X10))
% 54.42/54.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X10)))),
% 54.42/54.60      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 54.42/54.60  thf('160', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['158', '159'])).
% 54.42/54.60  thf('161', plain,
% 54.42/54.60      (![X5 : $i, X6 : $i]:
% 54.42/54.60         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 54.42/54.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 54.42/54.60      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 54.42/54.60  thf('162', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (m1_subset_1 @ (k3_subset_1 @ X0 @ (k9_subset_1 @ X0 @ X1 @ X0)) @ 
% 54.42/54.60          (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['160', '161'])).
% 54.42/54.60  thf('163', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['158', '159'])).
% 54.42/54.60  thf('164', plain,
% 54.42/54.60      (![X3 : $i, X4 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 54.42/54.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 54.42/54.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 54.42/54.60  thf('165', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         ((k3_subset_1 @ X0 @ (k9_subset_1 @ X0 @ X1 @ X0))
% 54.42/54.60           = (k4_xboole_0 @ X0 @ (k9_subset_1 @ X0 @ X1 @ X0)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['163', '164'])).
% 54.42/54.60  thf('166', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (m1_subset_1 @ (k4_xboole_0 @ X0 @ (k9_subset_1 @ X0 @ X1 @ X0)) @ 
% 54.42/54.60          (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['162', '165'])).
% 54.42/54.60  thf(d2_tops_1, axiom,
% 54.42/54.60    (![A:$i]:
% 54.42/54.60     ( ( l1_pre_topc @ A ) =>
% 54.42/54.60       ( ![B:$i]:
% 54.42/54.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.42/54.60           ( ( k2_tops_1 @ A @ B ) =
% 54.42/54.60             ( k9_subset_1 @
% 54.42/54.60               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 54.42/54.60               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 54.42/54.60  thf('167', plain,
% 54.42/54.60      (![X44 : $i, X45 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 54.42/54.60          | ((k2_tops_1 @ X45 @ X44)
% 54.42/54.60              = (k9_subset_1 @ (u1_struct_0 @ X45) @ 
% 54.42/54.60                 (k2_pre_topc @ X45 @ X44) @ 
% 54.42/54.60                 (k2_pre_topc @ X45 @ (k3_subset_1 @ (u1_struct_0 @ X45) @ X44))))
% 54.42/54.60          | ~ (l1_pre_topc @ X45))),
% 54.42/54.60      inference('cnf', [status(esa)], [d2_tops_1])).
% 54.42/54.60  thf('168', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (l1_pre_topc @ X0)
% 54.42/54.60          | ((k2_tops_1 @ X0 @ 
% 54.42/54.60              (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 54.42/54.60               (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (u1_struct_0 @ X0))))
% 54.42/54.60              = (k9_subset_1 @ (u1_struct_0 @ X0) @ 
% 54.42/54.60                 (k2_pre_topc @ X0 @ 
% 54.42/54.60                  (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 54.42/54.60                   (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (u1_struct_0 @ X0)))) @ 
% 54.42/54.60                 (k2_pre_topc @ X0 @ 
% 54.42/54.60                  (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 54.42/54.60                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 54.42/54.60                    (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (u1_struct_0 @ X0))))))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['166', '167'])).
% 54.42/54.60  thf('169', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['158', '159'])).
% 54.42/54.60  thf('170', plain,
% 54.42/54.60      (![X13 : $i, X14 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 54.42/54.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 54.42/54.60      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 54.42/54.60  thf('171', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k9_subset_1 @ X0 @ X1 @ X0)))
% 54.42/54.60           = (k9_subset_1 @ X0 @ X1 @ X0))),
% 54.42/54.60      inference('sup-', [status(thm)], ['169', '170'])).
% 54.42/54.60  thf('172', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         ((k3_subset_1 @ X0 @ (k9_subset_1 @ X0 @ X1 @ X0))
% 54.42/54.60           = (k4_xboole_0 @ X0 @ (k9_subset_1 @ X0 @ X1 @ X0)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['163', '164'])).
% 54.42/54.60  thf('173', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ (k9_subset_1 @ X0 @ X1 @ X0)))
% 54.42/54.60           = (k9_subset_1 @ X0 @ X1 @ X0))),
% 54.42/54.60      inference('demod', [status(thm)], ['171', '172'])).
% 54.42/54.60  thf('174', plain,
% 54.42/54.60      (![X0 : $i, X1 : $i]:
% 54.42/54.60         (~ (l1_pre_topc @ X0)
% 54.42/54.60          | ((k2_tops_1 @ X0 @ 
% 54.42/54.60              (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 54.42/54.60               (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (u1_struct_0 @ X0))))
% 54.42/54.60              = (k9_subset_1 @ (u1_struct_0 @ X0) @ 
% 54.42/54.60                 (k2_pre_topc @ X0 @ 
% 54.42/54.60                  (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 54.42/54.60                   (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (u1_struct_0 @ X0)))) @ 
% 54.42/54.60                 (k2_pre_topc @ X0 @ 
% 54.42/54.60                  (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (u1_struct_0 @ X0))))))),
% 54.42/54.60      inference('demod', [status(thm)], ['168', '173'])).
% 54.42/54.60  thf('175', plain,
% 54.42/54.60      ((((k2_tops_1 @ sk_A @ 
% 54.42/54.60          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))
% 54.42/54.60          = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 54.42/54.60             (k2_pre_topc @ sk_A @ 
% 54.42/54.60              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))))
% 54.42/54.60        | ~ (l1_pre_topc @ sk_A))),
% 54.42/54.60      inference('sup+', [status(thm)], ['157', '174'])).
% 54.42/54.60  thf('176', plain,
% 54.42/54.60      (((sk_B)
% 54.42/54.60         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['85', '148', '151', '156'])).
% 54.42/54.60  thf('177', plain,
% 54.42/54.60      (((k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 54.42/54.60         = (k2_tops_1 @ sk_A @ sk_B))),
% 54.42/54.60      inference('demod', [status(thm)], ['22', '23', '28'])).
% 54.42/54.60  thf('178', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['43', '44'])).
% 54.42/54.60  thf('179', plain,
% 54.42/54.60      ((m1_subset_1 @ 
% 54.42/54.60        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['15', '30'])).
% 54.42/54.60  thf('180', plain,
% 54.42/54.60      (![X13 : $i, X14 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 54.42/54.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 54.42/54.60      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 54.42/54.60  thf('181', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 54.42/54.60         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['179', '180'])).
% 54.42/54.60  thf('182', plain,
% 54.42/54.60      (((k1_tops_1 @ sk_A @ sk_B)
% 54.42/54.60         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 54.42/54.60      inference('demod', [status(thm)], ['36', '37', '38'])).
% 54.42/54.60  thf('183', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 54.42/54.60         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 54.42/54.60      inference('demod', [status(thm)], ['181', '182'])).
% 54.42/54.60  thf('184', plain,
% 54.42/54.60      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 54.42/54.60         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 54.42/54.60      inference('sup+', [status(thm)], ['178', '183'])).
% 54.42/54.60  thf('185', plain,
% 54.42/54.60      (((sk_B)
% 54.42/54.60         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['85', '148', '151', '156'])).
% 54.42/54.60  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 54.42/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.42/54.60  thf('187', plain,
% 54.42/54.60      (((k2_tops_1 @ sk_A @ sk_B)
% 54.42/54.60         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 54.42/54.60            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 54.42/54.60            (k2_pre_topc @ sk_A @ sk_B)))),
% 54.42/54.60      inference('demod', [status(thm)],
% 54.42/54.60                ['175', '176', '177', '184', '185', '186'])).
% 54.42/54.60  thf('188', plain,
% 54.42/54.60      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['3', '4'])).
% 54.42/54.60  thf('189', plain,
% 54.42/54.60      (![X3 : $i, X4 : $i]:
% 54.42/54.60         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 54.42/54.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 54.42/54.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 54.42/54.60  thf('190', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['188', '189'])).
% 54.42/54.60  thf('191', plain,
% 54.42/54.60      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 54.42/54.60      inference('demod', [status(thm)], ['60', '65', '187', '190'])).
% 54.42/54.60  thf('192', plain,
% 54.42/54.60      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['3', '4'])).
% 54.42/54.60  thf('193', plain,
% 54.42/54.60      (![X36 : $i, X37 : $i, X38 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 54.42/54.60          | ~ (r1_tarski @ X38 @ (k3_subset_1 @ X37 @ X36))
% 54.42/54.60          | (r1_xboole_0 @ X38 @ X36)
% 54.42/54.60          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 54.42/54.60      inference('cnf', [status(esa)], [t43_subset_1])).
% 54.42/54.60  thf('194', plain,
% 54.42/54.60      (![X0 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.42/54.60          | (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 54.42/54.60          | ~ (r1_tarski @ X0 @ 
% 54.42/54.60               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['192', '193'])).
% 54.42/54.60  thf('195', plain,
% 54.42/54.60      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))
% 54.42/54.60         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 54.42/54.60      inference('sup-', [status(thm)], ['188', '189'])).
% 54.42/54.60  thf('196', plain,
% 54.42/54.60      (![X0 : $i]:
% 54.42/54.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 54.42/54.60          | (r1_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 54.42/54.60          | ~ (r1_tarski @ X0 @ 
% 54.42/54.60               (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B))))),
% 54.42/54.60      inference('demod', [status(thm)], ['194', '195'])).
% 54.42/54.60  thf('197', plain,
% 54.42/54.60      (((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 54.42/54.60        | ~ (m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 54.42/54.60      inference('sup-', [status(thm)], ['191', '196'])).
% 54.42/54.60  thf('198', plain,
% 54.42/54.60      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 54.42/54.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 54.42/54.60      inference('demod', [status(thm)], ['33', '39'])).
% 54.42/54.60  thf('199', plain,
% 54.42/54.60      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))),
% 54.42/54.60      inference('demod', [status(thm)], ['197', '198'])).
% 54.42/54.60  thf('200', plain, ($false), inference('demod', [status(thm)], ['0', '199'])).
% 54.42/54.60  
% 54.42/54.60  % SZS output end Refutation
% 54.42/54.60  
% 54.42/54.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
