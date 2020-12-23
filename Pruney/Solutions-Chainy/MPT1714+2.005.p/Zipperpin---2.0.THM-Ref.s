%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pFiLGBHaGV

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 906 expanded)
%              Number of leaves         :   26 ( 270 expanded)
%              Depth                    :   30
%              Number of atoms          : 1021 (12983 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['8'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( r1_tsep_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('11',plain,
    ( ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_tsep_1 @ X19 @ X18 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('27',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('30',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('33',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','59'])).

thf('61',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('62',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('72',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( r1_tsep_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('74',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('76',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('78',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('79',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('80',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('81',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('82',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_tsep_1 @ X19 @ X18 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('83',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('86',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('89',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('91',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('93',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X18 ) )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('95',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['78','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('98',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('101',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( l1_struct_0 @ X21 )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( r1_tsep_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('103',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['76','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('106',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('109',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['110'])).

thf('112',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('114',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['110'])).

thf('115',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['110'])).

thf('117',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('118',plain,(
    r1_tsep_1 @ sk_D @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['112','115','116','117'])).

thf('119',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( l1_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['74','118'])).

thf('120',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['1','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('122',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['110'])).

thf('124',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('125',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['110'])).

thf('126',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['112','115','117','126','116'])).

thf('128',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['123','127'])).

thf('129',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['122','128'])).

thf('130',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['66','67'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['130','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pFiLGBHaGV
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:34 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 108 iterations in 0.043s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(dt_l1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.50  thf('0', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('1', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('2', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('3', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('4', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('5', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('6', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('7', plain, (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf(t23_tmap_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.50                   ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.50                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.22/0.50                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.22/0.50                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50            ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50                  ( ![D:$i]:
% 0.22/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.50                      ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.50                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.22/0.50                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.22/0.50                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_C_1 @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_D @ sk_C_1)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('split', [status(esa)], ['8'])).
% 0.22/0.50  thf(symmetry_r1_tsep_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.22/0.50       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X20 : $i, X21 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X20)
% 0.22/0.50          | ~ (l1_struct_0 @ X21)
% 0.22/0.50          | (r1_tsep_1 @ X21 @ X20)
% 0.22/0.50          | ~ (r1_tsep_1 @ X20 @ X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((((r1_tsep_1 @ sk_C_1 @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_C_1)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | (r1_tsep_1 @ sk_C_1 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '11'])).
% 0.22/0.50  thf('13', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_m1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.50          | (l1_pre_topc @ X16)
% 0.22/0.50          | ~ (l1_pre_topc @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_C_1 @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_C_1 @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '18'])).
% 0.22/0.50  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.50          | (l1_pre_topc @ X16)
% 0.22/0.50          | ~ (l1_pre_topc @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_C_1 @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['19', '24'])).
% 0.22/0.50  thf(d3_tsep_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_struct_0 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( l1_struct_0 @ B ) =>
% 0.22/0.50           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.22/0.50             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X18)
% 0.22/0.50          | ~ (r1_tsep_1 @ X19 @ X18)
% 0.22/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.22/0.50          | ~ (l1_struct_0 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_C_1)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '27'])).
% 0.22/0.50  thf('29', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '30'])).
% 0.22/0.50  thf('32', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.50  thf(t3_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.50          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.50          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.50          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.50          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.50          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.22/0.50          | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['33', '39'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.50  thf('42', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t4_tsep_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.50               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.22/0.50                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X22 @ X23)
% 0.22/0.50          | ~ (m1_pre_topc @ X22 @ X24)
% 0.22/0.50          | (r1_tarski @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X24))
% 0.22/0.50          | ~ (m1_pre_topc @ X24 @ X23)
% 0.22/0.50          | ~ (l1_pre_topc @ X23)
% 0.22/0.50          | ~ (v2_pre_topc @ X23))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ sk_A)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.50          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.50          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      ((~ (m1_pre_topc @ sk_B @ sk_C_1)
% 0.22/0.50        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['42', '48'])).
% 0.22/0.50  thf('50', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X10 : $i, X12 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('53', plain,
% 0.22/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.50  thf(l3_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X7 @ X8)
% 0.22/0.50          | (r2_hidden @ X7 @ X9)
% 0.22/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.50  thf('56', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)
% 0.22/0.50          | (r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_B)) @ 
% 0.22/0.50             (u1_struct_0 @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['41', '55'])).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.50          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.50          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)
% 0.22/0.50          | ~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.50          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['40', '59'])).
% 0.22/0.50  thf('61', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X18)
% 0.22/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.22/0.50          | (r1_tsep_1 @ X19 @ X18)
% 0.22/0.50          | ~ (l1_struct_0 @ X19))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.50  thf('62', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.22/0.50         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_B)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '62'])).
% 0.22/0.50  thf('64', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X16 @ X17)
% 0.22/0.50          | (l1_pre_topc @ X16)
% 0.22/0.50          | ~ (l1_pre_topc @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('66', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.50  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('68', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['66', '67'])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['63', '68'])).
% 0.22/0.50  thf('70', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.22/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '69'])).
% 0.22/0.50  thf('71', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('demod', [status(thm)], ['70', '71'])).
% 0.22/0.50  thf('73', plain,
% 0.22/0.50      (![X20 : $i, X21 : $i]:
% 0.22/0.50         (~ (l1_struct_0 @ X20)
% 0.22/0.50          | ~ (l1_struct_0 @ X21)
% 0.22/0.50          | (r1_tsep_1 @ X21 @ X20)
% 0.22/0.50          | ~ (r1_tsep_1 @ X20 @ X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.50  thf('74', plain,
% 0.22/0.50      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.22/0.50  thf('75', plain,
% 0.22/0.50      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('76', plain,
% 0.22/0.50      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('77', plain,
% 0.22/0.50      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('79', plain,
% 0.22/0.50      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('80', plain,
% 0.22/0.50      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('81', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_C_1 @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('split', [status(esa)], ['8'])).
% 0.22/0.51  thf('82', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X18)
% 0.22/0.51          | ~ (r1_tsep_1 @ X19 @ X18)
% 0.22/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.22/0.51          | ~ (l1_struct_0 @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.51  thf('83', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_C_1)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['81', '82'])).
% 0.22/0.51  thf('84', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['80', '83'])).
% 0.22/0.51  thf('85', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('86', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['84', '85'])).
% 0.22/0.51  thf('87', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['79', '86'])).
% 0.22/0.51  thf('88', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('89', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['87', '88'])).
% 0.22/0.51  thf('90', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.51  thf('91', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.51  thf('92', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.22/0.51          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.51  thf('93', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.22/0.51  thf('94', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X18)
% 0.22/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X18))
% 0.22/0.51          | (r1_tsep_1 @ X19 @ X18)
% 0.22/0.51          | ~ (l1_struct_0 @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.51  thf('95', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_B)
% 0.22/0.51         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.51  thf('96', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_B)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.51         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['78', '95'])).
% 0.22/0.51  thf('97', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['66', '67'])).
% 0.22/0.51  thf('98', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['96', '97'])).
% 0.22/0.51  thf('99', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['77', '98'])).
% 0.22/0.51  thf('100', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('101', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['99', '100'])).
% 0.22/0.51  thf('102', plain,
% 0.22/0.51      (![X20 : $i, X21 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X20)
% 0.22/0.51          | ~ (l1_struct_0 @ X21)
% 0.22/0.51          | (r1_tsep_1 @ X21 @ X20)
% 0.22/0.51          | ~ (r1_tsep_1 @ X20 @ X21))),
% 0.22/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.51  thf('103', plain,
% 0.22/0.51      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['101', '102'])).
% 0.22/0.51  thf('104', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.22/0.51         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['76', '103'])).
% 0.22/0.51  thf('105', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('106', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['104', '105'])).
% 0.22/0.51  thf('107', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['75', '106'])).
% 0.22/0.51  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['66', '67'])).
% 0.22/0.51  thf('109', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['107', '108'])).
% 0.22/0.51  thf('110', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('111', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.22/0.51      inference('split', [status(esa)], ['110'])).
% 0.22/0.51  thf('112', plain,
% 0.22/0.51      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['109', '111'])).
% 0.22/0.51  thf('113', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['99', '100'])).
% 0.22/0.51  thf('114', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.22/0.51      inference('split', [status(esa)], ['110'])).
% 0.22/0.51  thf('115', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_C_1 @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['113', '114'])).
% 0.22/0.51  thf('116', plain,
% 0.22/0.51      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.22/0.51      inference('split', [status(esa)], ['110'])).
% 0.22/0.51  thf('117', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_D @ sk_C_1)) | ((r1_tsep_1 @ sk_C_1 @ sk_D))),
% 0.22/0.51      inference('split', [status(esa)], ['8'])).
% 0.22/0.51  thf('118', plain, (((r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['112', '115', '116', '117'])).
% 0.22/0.51  thf('119', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_D @ sk_B)
% 0.22/0.51        | ~ (l1_struct_0 @ sk_D)
% 0.22/0.51        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['74', '118'])).
% 0.22/0.51  thf('120', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_D)
% 0.22/0.51        | ~ (l1_struct_0 @ sk_B)
% 0.22/0.51        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '119'])).
% 0.22/0.51  thf('121', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('122', plain, ((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['120', '121'])).
% 0.22/0.51  thf('123', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.22/0.51      inference('split', [status(esa)], ['110'])).
% 0.22/0.51  thf('124', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.22/0.51      inference('demod', [status(thm)], ['70', '71'])).
% 0.22/0.51  thf('125', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.22/0.51      inference('split', [status(esa)], ['110'])).
% 0.22/0.51  thf('126', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['124', '125'])).
% 0.22/0.51  thf('127', plain, (~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)],
% 0.22/0.51                ['112', '115', '117', '126', '116'])).
% 0.22/0.51  thf('128', plain, (~ (r1_tsep_1 @ sk_D @ sk_B)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['123', '127'])).
% 0.22/0.51  thf('129', plain, (~ (l1_struct_0 @ sk_B)),
% 0.22/0.51      inference('clc', [status(thm)], ['122', '128'])).
% 0.22/0.51  thf('130', plain, (~ (l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '129'])).
% 0.22/0.51  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['66', '67'])).
% 0.22/0.51  thf('132', plain, ($false), inference('demod', [status(thm)], ['130', '131'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
