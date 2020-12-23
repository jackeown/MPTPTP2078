%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dEdEssPV2Q

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 212 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   20
%              Number of atoms          :  550 (2163 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(t22_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( m1_pre_topc @ B @ C )
               => ( ~ ( r1_tsep_1 @ B @ C )
                  & ~ ( r1_tsep_1 @ C @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ( m1_pre_topc @ B @ C )
                 => ( ~ ( r1_tsep_1 @ B @ C )
                    & ~ ( r1_tsep_1 @ C @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_tmap_1])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('14',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['16'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('19',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('29',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_tsep_1 @ X10 @ X9 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('31',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('34',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['12','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('37',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('39',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['11','39'])).

thf('41',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('42',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('43',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['16'])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_tsep_1 @ X10 @ X9 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('47',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('50',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('53',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('55',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['42','55'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('57',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['41','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('63',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['16'])).

thf('65',plain,(
    r1_tsep_1 @ sk_C @ sk_B ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['40','65'])).

thf('67',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dEdEssPV2Q
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:21:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 50 iterations in 0.020s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(dt_l1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.48  thf('0', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf(t22_tmap_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.48               ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.48                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.48              ( ![C:$i]:
% 0.21/0.48                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.48                  ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.48                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.21/0.48  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t1_tsep_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48           ( m1_subset_1 @
% 0.21/0.48             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.48          | (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.48          | ~ (l1_pre_topc @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_C)
% 0.21/0.48        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_m1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.48  thf('6', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '8'])).
% 0.21/0.48  thf(t3_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.48  thf('11', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('13', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('14', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('15', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('16', plain, (((r1_tsep_1 @ sk_B @ sk_C) | (r1_tsep_1 @ sk_C @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_C @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['16'])).
% 0.21/0.48  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.48       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X11)
% 0.21/0.48          | ~ (l1_struct_0 @ X12)
% 0.21/0.48          | (r1_tsep_1 @ X12 @ X11)
% 0.21/0.48          | ~ (r1_tsep_1 @ X11 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((((r1_tsep_1 @ sk_B @ sk_C)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_tsep_1 @ sk_B @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '19'])).
% 0.21/0.48  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.48  thf('23', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_B @ sk_C)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['20', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_B @ sk_C)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '26'])).
% 0.21/0.48  thf('28', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf(d3_tsep_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_struct_0 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( l1_struct_0 @ B ) =>
% 0.21/0.48           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.48             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X9)
% 0.21/0.48          | ~ (r1_tsep_1 @ X10 @ X9)
% 0.21/0.48          | (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.48          | ~ (l1_struct_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '31'])).
% 0.21/0.48  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '34'])).
% 0.21/0.48  thf('36', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf(t69_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.48       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r1_tarski @ X0 @ X1)
% 0.21/0.48          | (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.48         | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '39'])).
% 0.21/0.48  thf('41', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('42', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('43', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('44', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['16'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X9)
% 0.21/0.48          | ~ (r1_tsep_1 @ X10 @ X9)
% 0.21/0.48          | (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.48          | ~ (l1_struct_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['44', '47'])).
% 0.21/0.48  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['43', '50'])).
% 0.21/0.48  thf('52', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r1_tarski @ X0 @ X1)
% 0.21/0.48          | (v1_xboole_0 @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.48         | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['42', '55'])).
% 0.21/0.48  thf(fc2_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      (![X8 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.21/0.48          | ~ (l1_struct_0 @ X8)
% 0.21/0.48          | (v2_struct_0 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      ((((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.48  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('60', plain, ((~ (l1_struct_0 @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.48  thf('61', plain, ((~ (l1_pre_topc @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['41', '60'])).
% 0.21/0.48  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('63', plain, (~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.48  thf('64', plain, (((r1_tsep_1 @ sk_C @ sk_B)) | ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.21/0.48      inference('split', [status(esa)], ['16'])).
% 0.21/0.48  thf('65', plain, (((r1_tsep_1 @ sk_C @ sk_B))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.21/0.48  thf('66', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['40', '65'])).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      (![X8 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.21/0.48          | ~ (l1_struct_0 @ X8)
% 0.21/0.48          | (v2_struct_0 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.48  thf('68', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.48  thf('69', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('70', plain, (~ (l1_struct_0 @ sk_B)),
% 0.21/0.48      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.48  thf('71', plain, (~ (l1_pre_topc @ sk_B)),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '70'])).
% 0.21/0.48  thf('72', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('73', plain, ($false), inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
