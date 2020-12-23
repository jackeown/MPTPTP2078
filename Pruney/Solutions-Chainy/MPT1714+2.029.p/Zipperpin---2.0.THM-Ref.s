%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9dKHu4U7iY

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 760 expanded)
%              Number of leaves         :   23 ( 226 expanded)
%              Depth                    :   27
%              Number of atoms          :  830 (10553 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(t23_tmap_1,conjecture,(
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
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) )
                      | ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) )).

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
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( m1_pre_topc @ B @ C )
                     => ( ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) )
                        | ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tmap_1])).

thf('8',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('11',plain,
    ( ( ( r1_tsep_1 @ sk_C @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_C @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_tsep_1 @ X10 @ X9 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('27',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('30',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('33',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('38',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ( r1_tsep_1 @ X10 @ X9 )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('45',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['2','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('55',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('57',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('61',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_tsep_1 @ X10 @ X9 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('66',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['15','16'])).

thf('69',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('72',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('74',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ( r1_tsep_1 @ X10 @ X9 )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('76',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['61','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('79',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['60','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('82',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('84',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['59','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('87',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['58','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('90',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('95',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['91'])).

thf('96',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['91'])).

thf('98',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('99',plain,(
    r1_tsep_1 @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['93','96','97','98'])).

thf('100',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( l1_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['57','99'])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['1','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('103',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['91'])).

thf('105',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('106',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['91'])).

thf('107',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['93','96','98','107','97'])).

thf('109',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['104','108'])).

thf('110',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['103','109'])).

thf('111',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['111','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9dKHu4U7iY
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:27:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 77 iterations in 0.026s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(dt_l1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.48  thf('0', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('1', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('2', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('3', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('4', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('5', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('6', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('7', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf(t23_tmap_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.48               ( ![D:$i]:
% 0.21/0.48                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.48                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.48                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.21/0.48                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.48                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.48              ( ![C:$i]:
% 0.21/0.48                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.48                  ( ![D:$i]:
% 0.21/0.48                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.48                      ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.48                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.21/0.48                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.48                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.21/0.48  thf('8', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['8'])).
% 0.21/0.48  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.48       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X11)
% 0.21/0.48          | ~ (l1_struct_0 @ X12)
% 0.21/0.48          | (r1_tsep_1 @ X12 @ X11)
% 0.21/0.48          | ~ (r1_tsep_1 @ X11 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((((r1_tsep_1 @ sk_C @ sk_D)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.48         | (r1_tsep_1 @ sk_C @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.48  thf('13', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_m1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.48  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_C @ sk_D)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_C @ sk_D)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '18'])).
% 0.21/0.48  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.48  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '24'])).
% 0.21/0.48  thf(d3_tsep_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_struct_0 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( l1_struct_0 @ B ) =>
% 0.21/0.48           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.48             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X9)
% 0.21/0.48          | ~ (r1_tsep_1 @ X10 @ X9)
% 0.21/0.48          | (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.48          | ~ (l1_struct_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '27'])).
% 0.21/0.48  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '30'])).
% 0.21/0.48  thf('32', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (((r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t1_tsep_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48           ( m1_subset_1 @
% 0.21/0.48             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.48          | (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.48          | ~ (l1_pre_topc @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_C)
% 0.21/0.48        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf(t3_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]:
% 0.21/0.48         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.48  thf('40', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf(t63_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.48       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.48          | ~ (r1_xboole_0 @ X1 @ X2)
% 0.21/0.48          | (r1_xboole_0 @ X0 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)
% 0.21/0.48          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['33', '42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X9)
% 0.21/0.48          | ~ (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.48          | (r1_tsep_1 @ X10 @ X9)
% 0.21/0.48          | ~ (l1_struct_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.48         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.48         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '45'])).
% 0.21/0.48  thf('47', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.48  thf('49', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.48  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['46', '51'])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '52'])).
% 0.21/0.48  thf('54', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X11)
% 0.21/0.48          | ~ (l1_struct_0 @ X12)
% 0.21/0.48          | (r1_tsep_1 @ X12 @ X11)
% 0.21/0.48          | ~ (r1_tsep_1 @ X11 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.48  thf('58', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('59', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('60', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('61', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('62', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('63', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('64', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('split', [status(esa)], ['8'])).
% 0.21/0.48  thf('65', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X9)
% 0.21/0.48          | ~ (r1_tsep_1 @ X10 @ X9)
% 0.21/0.48          | (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.48          | ~ (l1_struct_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.48  thf('66', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['63', '66'])).
% 0.21/0.48  thf('68', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('69', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.48  thf('70', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['62', '69'])).
% 0.21/0.48  thf('71', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('72', plain,
% 0.21/0.48      (((r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.48  thf('73', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)
% 0.21/0.48          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('74', plain,
% 0.21/0.48      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.48  thf('75', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X9)
% 0.21/0.48          | ~ (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.48          | (r1_tsep_1 @ X10 @ X9)
% 0.21/0.48          | ~ (l1_struct_0 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.48  thf('76', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.48         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.48  thf('77', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.48         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['61', '76'])).
% 0.21/0.48  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf('79', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.48  thf('80', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['60', '79'])).
% 0.21/0.48  thf('81', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('82', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['80', '81'])).
% 0.21/0.48  thf('83', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X11)
% 0.21/0.48          | ~ (l1_struct_0 @ X12)
% 0.21/0.48          | (r1_tsep_1 @ X12 @ X11)
% 0.21/0.48          | ~ (r1_tsep_1 @ X11 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.48  thf('84', plain,
% 0.21/0.48      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.48  thf('85', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.48         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['59', '84'])).
% 0.21/0.48  thf('86', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('87', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['85', '86'])).
% 0.21/0.48  thf('88', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['58', '87'])).
% 0.21/0.48  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf('90', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['88', '89'])).
% 0.21/0.48  thf('91', plain,
% 0.21/0.48      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('92', plain,
% 0.21/0.48      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['91'])).
% 0.21/0.48  thf('93', plain,
% 0.21/0.48      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['90', '92'])).
% 0.21/0.49  thf('94', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['80', '81'])).
% 0.21/0.49  thf('95', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['91'])).
% 0.21/0.49  thf('96', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['94', '95'])).
% 0.21/0.49  thf('97', plain,
% 0.21/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.49      inference('split', [status(esa)], ['91'])).
% 0.21/0.49  thf('98', plain, (((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.21/0.49      inference('split', [status(esa)], ['8'])).
% 0.21/0.49  thf('99', plain, (((r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['93', '96', '97', '98'])).
% 0.21/0.49  thf('100', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.49        | ~ (l1_struct_0 @ sk_D)
% 0.21/0.49        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['57', '99'])).
% 0.21/0.49  thf('101', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_D)
% 0.21/0.49        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.49        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '100'])).
% 0.21/0.49  thf('102', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('103', plain, ((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['101', '102'])).
% 0.21/0.49  thf('104', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['91'])).
% 0.21/0.49  thf('105', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.49  thf('106', plain,
% 0.21/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.49      inference('split', [status(esa)], ['91'])).
% 0.21/0.49  thf('107', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['105', '106'])).
% 0.21/0.49  thf('108', plain, (~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)],
% 0.21/0.49                ['93', '96', '98', '107', '97'])).
% 0.21/0.49  thf('109', plain, (~ (r1_tsep_1 @ sk_D @ sk_B)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['104', '108'])).
% 0.21/0.49  thf('110', plain, (~ (l1_struct_0 @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['103', '109'])).
% 0.21/0.49  thf('111', plain, (~ (l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '110'])).
% 0.21/0.49  thf('112', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('113', plain, ($false), inference('demod', [status(thm)], ['111', '112'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
