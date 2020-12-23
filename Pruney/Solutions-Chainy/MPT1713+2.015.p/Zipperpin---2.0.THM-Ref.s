%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yQPeAluOzI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 227 expanded)
%              Number of leaves         :   29 (  78 expanded)
%              Depth                    :   20
%              Number of atoms          :  602 (2263 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    m1_pre_topc @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['18'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( r1_tsep_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('21',plain,
    ( ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['6','7'])).

thf('31',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_tsep_1 @ X17 @ X16 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('33',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('36',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['6','7'])).

thf('39',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['13','43'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('45',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('46',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('49',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('52',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_tsep_1 @ X17 @ X16 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('53',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('56',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['6','7'])).

thf('59',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['48','61'])).

thf('63',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('69',plain,(
    ~ ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B_1 )
    | ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('71',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['46','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yQPeAluOzI
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:25:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 71 iterations in 0.028s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.49  thf(dt_l1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.49  thf('0', plain, (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf(t22_tmap_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49               ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.49                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49                  ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.49                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.21/0.49  thf('1', plain, ((m1_pre_topc @ sk_B_1 @ sk_C_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t1_tsep_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( m1_subset_1 @
% 0.21/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X20 @ X21)
% 0.21/0.49          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.49          | ~ (l1_pre_topc @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_m1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.49          | (l1_pre_topc @ X13)
% 0.21/0.49          | ~ (l1_pre_topc @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('6', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '8'])).
% 0.21/0.49  thf(t3_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i]:
% 0.21/0.49         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf(t28_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (((k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.49         = (u1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B_1 @ sk_C_1) | (r1_tsep_1 @ sk_C_1 @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_B_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X18)
% 0.21/0.49          | ~ (l1_struct_0 @ X19)
% 0.21/0.49          | (r1_tsep_1 @ X19 @ X18)
% 0.21/0.49          | ~ (r1_tsep_1 @ X18 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((((r1_tsep_1 @ sk_B_1 @ sk_C_1)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_B_1)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | (r1_tsep_1 @ sk_B_1 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '21'])).
% 0.21/0.49  thf('23', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.49          | (l1_pre_topc @ X13)
% 0.21/0.49          | ~ (l1_pre_topc @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('25', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_C_1) | (r1_tsep_1 @ sk_B_1 @ sk_C_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((~ (l1_pre_topc @ sk_C_1) | (r1_tsep_1 @ sk_B_1 @ sk_C_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '28'])).
% 0.21/0.49  thf('30', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf(d3_tsep_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_struct_0 @ B ) =>
% 0.21/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X16)
% 0.21/0.49          | ~ (r1_tsep_1 @ X17 @ X16)
% 0.21/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.21/0.49          | ~ (l1_struct_0 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_B_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '33'])).
% 0.21/0.49  thf('35', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '36'])).
% 0.21/0.49  thf('38', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf(t4_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.21/0.49          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (((v1_xboole_0 @ 
% 0.21/0.49         (k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['13', '43'])).
% 0.21/0.49  thf(fc2_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X15 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.21/0.49          | ~ (l1_struct_0 @ X15)
% 0.21/0.49          | (v2_struct_0 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (((k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.49         = (u1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X16)
% 0.21/0.49          | ~ (r1_tsep_1 @ X17 @ X16)
% 0.21/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.21/0.49          | ~ (l1_struct_0 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_B_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['50', '53'])).
% 0.21/0.49  thf('55', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['49', '56'])).
% 0.21/0.49  thf('58', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (((v1_xboole_0 @ 
% 0.21/0.49         (k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['48', '61'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (![X15 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X15))
% 0.21/0.49          | ~ (l1_struct_0 @ X15)
% 0.21/0.49          | (v2_struct_0 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.49  thf('65', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      ((~ (l1_struct_0 @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['64', '65'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '66'])).
% 0.21/0.49  thf('68', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('69', plain, (~ ((r1_tsep_1 @ sk_B_1 @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_B_1)) | ((r1_tsep_1 @ sk_B_1 @ sk_C_1))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('71', plain, (((r1_tsep_1 @ sk_C_1 @ sk_B_1))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.21/0.49  thf('72', plain, (((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['46', '71'])).
% 0.21/0.49  thf('73', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('74', plain, (~ (l1_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('clc', [status(thm)], ['72', '73'])).
% 0.21/0.49  thf('75', plain, (~ (l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '74'])).
% 0.21/0.49  thf('76', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('77', plain, ($false), inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
