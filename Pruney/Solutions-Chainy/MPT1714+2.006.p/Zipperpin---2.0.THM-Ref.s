%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ByiXReKNS1

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 755 expanded)
%              Number of leaves         :   23 ( 223 expanded)
%              Depth                    :   30
%              Number of atoms          :  939 (11228 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('14',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['16'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( r1_tsep_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('19',plain,
    ( ( ( r1_tsep_1 @ sk_C @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_C @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['27','32'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_tsep_1 @ X17 @ X16 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('35',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['13','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('38',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['12','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('41',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('43',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      = ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['11','45'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('54',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['16'])).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_tsep_1 @ X17 @ X16 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('58',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('61',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('64',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      = ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C ) )
        | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['53','68'])).

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('71',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['52','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['51','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('81',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( r1_tsep_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('83',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['50','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('86',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['49','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['75','76'])).

thf('89',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['90'])).

thf('92',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('94',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['90'])).

thf('95',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['90'])).

thf('97',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['16'])).

thf('98',plain,(
    r1_tsep_1 @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['92','95','96','97'])).

thf('99',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['48','98'])).

thf('100',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('101',plain,
    ( ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['90'])).

thf('103',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('104',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('105',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['11','45'])).

thf('106',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('107',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['75','76'])).

thf('110',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('113',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['90'])).

thf('115',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['92','95','97','115','96'])).

thf('117',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['102','116'])).

thf('118',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['101','117'])).

thf('119',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['75','76'])).

thf('121',plain,(
    ~ ( l1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['0','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['122','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ByiXReKNS1
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 174 iterations in 0.050s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(dt_l1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.50  thf('0', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('1', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf(t23_tmap_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.50                   ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.50                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.20/0.50                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.50                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50                  ( ![D:$i]:
% 0.20/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.50                      ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.50                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.20/0.50                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.50                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.20/0.50  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t4_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.50               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.20/0.50                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.50          | ~ (m1_pre_topc @ X20 @ X22)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))
% 0.20/0.50          | ~ (m1_pre_topc @ X22 @ X21)
% 0.20/0.50          | ~ (l1_pre_topc @ X21)
% 0.20/0.50          | ~ (v2_pre_topc @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 0.20/0.50        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.50  thf('10', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('16', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['16'])).
% 0.20/0.50  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.50       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X18)
% 0.20/0.50          | ~ (l1_struct_0 @ X19)
% 0.20/0.50          | (r1_tsep_1 @ X19 @ X18)
% 0.20/0.50          | ~ (r1_tsep_1 @ X18 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((((r1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_C)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_tsep_1 @ sk_C @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '19'])).
% 0.20/0.50  thf('21', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_m1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.50          | (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('23', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_C @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_C @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '26'])).
% 0.20/0.50  thf('28', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.50          | (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('30', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('32', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '32'])).
% 0.20/0.50  thf(d3_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_struct_0 @ B ) =>
% 0.20/0.50           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.50             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X16)
% 0.20/0.50          | ~ (r1_tsep_1 @ X17 @ X16)
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.50          | ~ (l1_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_C)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_C)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '35'])).
% 0.20/0.50  thf('37', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '38'])).
% 0.20/0.50  thf('40', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf(t83_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((((k4_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.20/0.50          = (u1_struct_0 @ sk_C)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf(t106_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.20/0.50       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X5 @ X7)
% 0.20/0.50          | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50           | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_D))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '45'])).
% 0.20/0.50  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('53', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['16'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X16)
% 0.20/0.50          | ~ (r1_tsep_1 @ X17 @ X16)
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.50          | ~ (l1_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_C)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_C)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['55', '58'])).
% 0.20/0.50  thf('60', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['54', '61'])).
% 0.20/0.50  thf('63', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      ((((k4_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.20/0.50          = (u1_struct_0 @ sk_C)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X5 @ X7)
% 0.20/0.50          | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50           | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_D))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '68'])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X16)
% 0.20/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.50          | (r1_tsep_1 @ X17 @ X16)
% 0.20/0.50          | ~ (l1_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '71'])).
% 0.20/0.50  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.50          | (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('75', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.50  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['72', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['51', '78'])).
% 0.20/0.50  thf('80', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X18)
% 0.20/0.50          | ~ (l1_struct_0 @ X19)
% 0.20/0.50          | (r1_tsep_1 @ X19 @ X18)
% 0.20/0.50          | ~ (r1_tsep_1 @ X18 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.50  thf('83', plain,
% 0.20/0.50      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '83'])).
% 0.20/0.50  thf('85', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['49', '86'])).
% 0.20/0.50  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('89', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['87', '88'])).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['90'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['89', '91'])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['90'])).
% 0.20/0.50  thf('95', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.50  thf('96', plain,
% 0.20/0.50      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.50      inference('split', [status(esa)], ['90'])).
% 0.20/0.50  thf('97', plain, (((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.20/0.50      inference('split', [status(esa)], ['16'])).
% 0.20/0.50  thf('98', plain, (((r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['92', '95', '96', '97'])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      ((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['48', '98'])).
% 0.20/0.50  thf('100', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X16)
% 0.20/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.50          | (r1_tsep_1 @ X17 @ X16)
% 0.20/0.50          | ~ (l1_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('101', plain,
% 0.20/0.50      ((~ (l1_struct_0 @ sk_D)
% 0.20/0.50        | (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.50        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.50  thf('102', plain,
% 0.20/0.50      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['90'])).
% 0.20/0.50  thf('103', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('104', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('105', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '45'])).
% 0.20/0.50  thf('106', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X16)
% 0.20/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.50          | (r1_tsep_1 @ X17 @ X16)
% 0.20/0.50          | ~ (l1_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('107', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.50  thf('108', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['104', '107'])).
% 0.20/0.50  thf('109', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('110', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.50  thf('111', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['103', '110'])).
% 0.20/0.50  thf('112', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('113', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['111', '112'])).
% 0.20/0.50  thf('114', plain,
% 0.20/0.50      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['90'])).
% 0.20/0.50  thf('115', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.50  thf('116', plain, (~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['92', '95', '97', '115', '96'])).
% 0.20/0.50  thf('117', plain, (~ (r1_tsep_1 @ sk_D @ sk_B)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['102', '116'])).
% 0.20/0.50  thf('118', plain, ((~ (l1_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_D))),
% 0.20/0.50      inference('clc', [status(thm)], ['101', '117'])).
% 0.20/0.50  thf('119', plain, ((~ (l1_pre_topc @ sk_B) | ~ (l1_struct_0 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '118'])).
% 0.20/0.50  thf('120', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.50  thf('121', plain, (~ (l1_struct_0 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['119', '120'])).
% 0.20/0.50  thf('122', plain, (~ (l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '121'])).
% 0.20/0.50  thf('123', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('124', plain, ($false), inference('demod', [status(thm)], ['122', '123'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
