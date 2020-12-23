%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5JZfcQXCY2

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 226 expanded)
%              Number of leaves         :   28 (  77 expanded)
%              Depth                    :   21
%              Number of atoms          :  605 (2241 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X16 )
      | ( r1_tsep_1 @ X16 @ X15 )
      | ~ ( r1_tsep_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('21',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('31',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_struct_0 @ X13 )
      | ~ ( r1_tsep_1 @ X14 @ X13 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('33',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['15','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('36',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['14','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('39',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_xboole_0
      = ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['13','41'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('43',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('44',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('49',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['18'])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_struct_0 @ X13 )
      | ~ ( r1_tsep_1 @ X14 @ X13 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('53',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('56',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['6','7'])).

thf('59',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_xboole_0
      = ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['48','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('64',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['47','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('71',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['18'])).

thf('73',plain,(
    r1_tsep_1 @ sk_C @ sk_B ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['46','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5JZfcQXCY2
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 71 iterations in 0.028s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(dt_l1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('0', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf(t22_tmap_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49               ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.49                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49                  ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.49                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.20/0.49  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t1_tsep_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.49           ( m1_subset_1 @
% 0.20/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X17 : $i, X18 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.49          | (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.49          | ~ (l1_pre_topc @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((~ (l1_pre_topc @ sk_C)
% 0.20/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_m1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.49          | (l1_pre_topc @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('6', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '8'])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('11', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(l32_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.20/0.49         = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('15', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('16', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('17', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('18', plain, (((r1_tsep_1 @ sk_B @ sk_C) | (r1_tsep_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_C @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['18'])).
% 0.20/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X15)
% 0.20/0.49          | ~ (l1_struct_0 @ X16)
% 0.20/0.49          | (r1_tsep_1 @ X16 @ X15)
% 0.20/0.49          | ~ (r1_tsep_1 @ X15 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((((r1_tsep_1 @ sk_B @ sk_C)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_tsep_1 @ sk_B @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '21'])).
% 0.20/0.49  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.49          | (l1_pre_topc @ X10)
% 0.20/0.49          | ~ (l1_pre_topc @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('25', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_B @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_B @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '28'])).
% 0.20/0.49  thf('30', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf(d3_tsep_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_struct_0 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( l1_struct_0 @ B ) =>
% 0.20/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X13)
% 0.20/0.49          | ~ (r1_tsep_1 @ X14 @ X13)
% 0.20/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X13))
% 0.20/0.49          | ~ (l1_struct_0 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '33'])).
% 0.20/0.49  thf('35', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '36'])).
% 0.20/0.49  thf('38', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf(t83_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      ((((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.20/0.49          = (u1_struct_0 @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((((k1_xboole_0) = (u1_struct_0 @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['13', '41'])).
% 0.20/0.49  thf(fc2_struct_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X12 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (l1_struct_0 @ X12)
% 0.20/0.49          | (v2_struct_0 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.49         | (v2_struct_0 @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      ((((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.20/0.49         = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('49', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('50', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['18'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X13)
% 0.20/0.49          | ~ (r1_tsep_1 @ X14 @ X13)
% 0.20/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X13))
% 0.20/0.49          | ~ (l1_struct_0 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.49  thf('55', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['49', '56'])).
% 0.20/0.49  thf('58', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      ((((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.20/0.49          = (u1_struct_0 @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      ((((k1_xboole_0) = (u1_struct_0 @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['48', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (![X12 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.20/0.49          | ~ (l1_struct_0 @ X12)
% 0.20/0.49          | (v2_struct_0 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.49         | (v2_struct_0 @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.49  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      ((((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.49  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('68', plain, ((~ (l1_struct_0 @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('69', plain, ((~ (l1_pre_topc @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['47', '68'])).
% 0.20/0.49  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('71', plain, (~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.49  thf('72', plain, (((r1_tsep_1 @ sk_C @ sk_B)) | ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.20/0.49      inference('split', [status(esa)], ['18'])).
% 0.20/0.49  thf('73', plain, (((r1_tsep_1 @ sk_C @ sk_B))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 0.20/0.49  thf('74', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['46', '73'])).
% 0.20/0.49  thf('75', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('76', plain, (~ (l1_struct_0 @ sk_B)),
% 0.20/0.49      inference('clc', [status(thm)], ['74', '75'])).
% 0.20/0.49  thf('77', plain, (~ (l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '76'])).
% 0.20/0.49  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('79', plain, ($false), inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
