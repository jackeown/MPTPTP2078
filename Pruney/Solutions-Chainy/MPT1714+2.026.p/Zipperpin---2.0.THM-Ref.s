%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OKsbTpoxL5

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 785 expanded)
%              Number of leaves         :   25 ( 234 expanded)
%              Depth                    :   36
%              Number of atoms          :  839 (10809 expanded)
%              Number of equality atoms :    3 (  18 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('11',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_tsep_1 @ X13 @ X12 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('27',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('30',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('33',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('36',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_tsep_1 @ X13 @ X12 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('39',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('42',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('45',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('50',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('59',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['34','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('62',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['33','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('71',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['32','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('74',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['31','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('77',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('82',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['78'])).

thf('83',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['78'])).

thf('85',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('86',plain,(
    r1_tsep_1 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['80','83','84','85'])).

thf('87',plain,
    ( ~ ( l1_struct_0 @ sk_C )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['30','86'])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('90',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('92',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('94',plain,
    ( ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['3','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('97',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['2','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('100',plain,(
    r1_tsep_1 @ sk_D @ sk_B ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('102',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['1','102'])).

thf('104',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('105',plain,
    ( ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['78'])).

thf('107',plain,(
    r1_tsep_1 @ sk_D @ sk_B ),
    inference(demod,[status(thm)],['98','99'])).

thf('108',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['78'])).

thf('109',plain,(
    r1_tsep_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['78'])).

thf('111',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['106','111'])).

thf('113',plain,(
    ~ ( l1_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['105','112'])).

thf('114',plain,(
    ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['0','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['114','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OKsbTpoxL5
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:32:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 91 iterations in 0.033s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(dt_l1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('0', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('1', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('2', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('3', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('4', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('5', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('6', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('7', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf(t23_tmap_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.49                   ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.49                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.20/0.49                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.49                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49                  ( ![D:$i]:
% 0.20/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.49                      ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.49                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.20/0.49                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.49                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.20/0.49  thf('8', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X14)
% 0.20/0.49          | ~ (l1_struct_0 @ X15)
% 0.20/0.49          | (r1_tsep_1 @ X15 @ X14)
% 0.20/0.49          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((r1_tsep_1 @ sk_D @ sk_C)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_tsep_1 @ sk_D @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '11'])).
% 0.20/0.49  thf('13', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_m1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.49          | (l1_pre_topc @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['12', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '18'])).
% 0.20/0.49  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.49          | (l1_pre_topc @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '24'])).
% 0.20/0.49  thf(d3_tsep_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_struct_0 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( l1_struct_0 @ B ) =>
% 0.20/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X12)
% 0.20/0.49          | ~ (r1_tsep_1 @ X13 @ X12)
% 0.20/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (l1_struct_0 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '27'])).
% 0.20/0.49  thf('29', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('32', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('33', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('34', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('35', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('36', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X12)
% 0.20/0.49          | ~ (r1_tsep_1 @ X13 @ X12)
% 0.20/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (l1_struct_0 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.49  thf('41', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '42'])).
% 0.20/0.49  thf('44', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.49  thf('46', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t1_tsep_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.49           ( m1_subset_1 @
% 0.20/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.49          | (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.49          | ~ (l1_pre_topc @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_C)
% 0.20/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('49', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('52', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf(t12_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.20/0.49         = (u1_struct_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.49  thf(t70_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X2 @ X3)
% 0.20/0.49          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '56'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X12)
% 0.20/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.20/0.49          | (r1_tsep_1 @ X13 @ X12)
% 0.20/0.49          | ~ (l1_struct_0 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '59'])).
% 0.20/0.49  thf('61', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '62'])).
% 0.20/0.49  thf('64', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.49          | (l1_pre_topc @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('66', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.49  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('68', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['63', '68'])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X14)
% 0.20/0.49          | ~ (l1_struct_0 @ X15)
% 0.20/0.49          | (r1_tsep_1 @ X15 @ X14)
% 0.20/0.49          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      ((((r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('72', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '71'])).
% 0.20/0.49  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '74'])).
% 0.20/0.49  thf('76', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['78'])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['77', '79'])).
% 0.20/0.49  thf('81', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['63', '68'])).
% 0.20/0.49  thf('82', plain,
% 0.20/0.49      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['78'])).
% 0.20/0.49  thf('83', plain,
% 0.20/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.49  thf('84', plain,
% 0.20/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.49      inference('split', [status(esa)], ['78'])).
% 0.20/0.49  thf('85', plain, (((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf('86', plain, (((r1_tsep_1 @ sk_C @ sk_D))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['80', '83', '84', '85'])).
% 0.20/0.49  thf('87', plain,
% 0.20/0.49      ((~ (l1_struct_0 @ sk_C)
% 0.20/0.49        | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['30', '86'])).
% 0.20/0.49  thf('88', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_C)
% 0.20/0.49        | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '87'])).
% 0.20/0.49  thf('89', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('90', plain,
% 0.20/0.49      ((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.49  thf('91', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf('92', plain,
% 0.20/0.49      ((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.49  thf('93', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X12)
% 0.20/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.20/0.49          | (r1_tsep_1 @ X13 @ X12)
% 0.20/0.49          | ~ (l1_struct_0 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.49  thf('94', plain,
% 0.20/0.49      ((~ (l1_struct_0 @ sk_D)
% 0.20/0.49        | (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.49  thf('95', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_D)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '94'])).
% 0.20/0.49  thf('96', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('97', plain, ((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.49  thf('98', plain, ((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '97'])).
% 0.20/0.49  thf('99', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('100', plain, ((r1_tsep_1 @ sk_D @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.49  thf('101', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X14)
% 0.20/0.49          | ~ (l1_struct_0 @ X15)
% 0.20/0.49          | (r1_tsep_1 @ X15 @ X14)
% 0.20/0.49          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.49  thf('102', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['100', '101'])).
% 0.20/0.49  thf('103', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.49        | ~ (l1_struct_0 @ sk_D)
% 0.20/0.49        | (r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '102'])).
% 0.20/0.49  thf('104', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('105', plain, ((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.49      inference('demod', [status(thm)], ['103', '104'])).
% 0.20/0.49  thf('106', plain,
% 0.20/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['78'])).
% 0.20/0.49  thf('107', plain, ((r1_tsep_1 @ sk_D @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.49  thf('108', plain,
% 0.20/0.49      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['78'])).
% 0.20/0.49  thf('109', plain, (((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['107', '108'])).
% 0.20/0.49  thf('110', plain,
% 0.20/0.49      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.49      inference('split', [status(esa)], ['78'])).
% 0.20/0.49  thf('111', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['109', '110'])).
% 0.20/0.49  thf('112', plain, (~ (r1_tsep_1 @ sk_B @ sk_D)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['106', '111'])).
% 0.20/0.49  thf('113', plain, (~ (l1_struct_0 @ sk_D)),
% 0.20/0.49      inference('clc', [status(thm)], ['105', '112'])).
% 0.20/0.49  thf('114', plain, (~ (l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '113'])).
% 0.20/0.49  thf('115', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('116', plain, ($false), inference('demod', [status(thm)], ['114', '115'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
