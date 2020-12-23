%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L7YuFwWhRt

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 572 expanded)
%              Number of leaves         :   23 ( 173 expanded)
%              Depth                    :   26
%              Number of atoms          :  949 (8341 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf('2',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
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

thf('6',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_2 )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_tsep_1 @ X17 @ X16 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('9',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['17','22'])).

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

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
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

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X22 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C_2 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['23','42'])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('45',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
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
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('55',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( r1_tsep_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('57',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['1','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('60',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('63',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C_2 )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('70',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('71',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('72',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('73',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('74',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( r1_tsep_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('75',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_C_2 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_tsep_1 @ sk_D @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('78',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_tsep_1 @ sk_D @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_2 )
      | ( r1_tsep_1 @ sk_D @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('81',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_2 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_tsep_1 @ X17 @ X16 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('83',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('86',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['20','21'])).

thf('89',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_2 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('91',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X16 ) )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('93',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('96',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('99',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['64'])).

thf('101',plain,
    ( ~ ( r1_tsep_1 @ sk_C_2 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('103',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['64'])).

thf('104',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C_2 )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['64'])).

thf('106',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('107',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('108',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('109',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_struct_0 @ X18 )
      | ~ ( l1_struct_0 @ X19 )
      | ( r1_tsep_1 @ X19 @ X18 )
      | ~ ( r1_tsep_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('110',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('113',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['106','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('116',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['64'])).

thf('118',plain,
    ( ~ ( r1_tsep_1 @ sk_C_2 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('120',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['66','101','104','105','118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L7YuFwWhRt
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:38:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 110 iterations in 0.043s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(dt_l1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.50  thf('0', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('1', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('2', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('3', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('4', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('5', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
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
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_C_2 @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_D @ sk_C_2)) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('split', [status(esa)], ['6'])).
% 0.20/0.50  thf(d3_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_struct_0 @ B ) =>
% 0.20/0.50           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.50             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X16)
% 0.20/0.50          | ~ (r1_tsep_1 @ X17 @ X16)
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.50          | ~ (l1_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_2)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '9'])).
% 0.20/0.50  thf('11', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_m1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.50          | (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_C_2)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '15'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_C_2)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '16'])).
% 0.20/0.50  thf('18', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.50          | (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('22', plain, ((l1_pre_topc @ sk_C_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.50  thf(t3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.50  thf('25', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain, ((m1_pre_topc @ sk_B @ sk_A)),
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
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.50          | ~ (m1_pre_topc @ X20 @ X22)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X22))
% 0.20/0.50          | ~ (m1_pre_topc @ X22 @ X21)
% 0.20/0.50          | ~ (l1_pre_topc @ X21)
% 0.20/0.50          | ~ (v2_pre_topc @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((~ (m1_pre_topc @ sk_B @ sk_C_2)
% 0.20/0.50        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '31'])).
% 0.20/0.50  thf('33', plain, ((m1_pre_topc @ sk_B @ sk_C_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)
% 0.20/0.50          | (r2_hidden @ (sk_C_1 @ X0 @ (u1_struct_0 @ sk_B)) @ 
% 0.20/0.50             (u1_struct_0 @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.50          | ~ (r2_hidden @ X6 @ X7)
% 0.20/0.50          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ X1 @ X0)
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.50          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X16)
% 0.20/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.50          | (r1_tsep_1 @ X17 @ X16)
% 0.20/0.50          | ~ (l1_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '45'])).
% 0.20/0.50  thf('47', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X14 @ X15)
% 0.20/0.50          | (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (l1_pre_topc @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('49', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['46', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '52'])).
% 0.20/0.50  thf('54', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.50       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X18)
% 0.20/0.50          | ~ (l1_struct_0 @ X19)
% 0.20/0.50          | (r1_tsep_1 @ X19 @ X18)
% 0.20/0.50          | ~ (r1_tsep_1 @ X18 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '57'])).
% 0.20/0.50  thf('59', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '60'])).
% 0.20/0.50  thf('62', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['64'])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (~ ((r1_tsep_1 @ sk_D @ sk_C_2)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['63', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_C_2 @ sk_D)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['6'])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X18)
% 0.20/0.50          | ~ (l1_struct_0 @ X19)
% 0.20/0.50          | (r1_tsep_1 @ X19 @ X18)
% 0.20/0.50          | ~ (r1_tsep_1 @ X18 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      ((((r1_tsep_1 @ sk_D @ sk_C_2)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_2)
% 0.20/0.50         | (r1_tsep_1 @ sk_D @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['72', '75'])).
% 0.20/0.50  thf('77', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_C_2) | (r1_tsep_1 @ sk_D @ sk_C_2)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_C_2) | (r1_tsep_1 @ sk_D @ sk_C_2)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['71', '78'])).
% 0.20/0.50  thf('80', plain, ((l1_pre_topc @ sk_C_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_D @ sk_C_2)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X16)
% 0.20/0.50          | ~ (r1_tsep_1 @ X17 @ X16)
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.50          | ~ (l1_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('83', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_2)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['70', '83'])).
% 0.20/0.50  thf('85', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_C_2)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_C_2)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['69', '86'])).
% 0.20/0.50  thf('88', plain, ((l1_pre_topc @ sk_C_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('89', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_2)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['87', '88'])).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_2))
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X16)
% 0.20/0.50          | ~ (r1_xboole_0 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X16))
% 0.20/0.50          | (r1_tsep_1 @ X17 @ X16)
% 0.20/0.50          | ~ (l1_struct_0 @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['68', '93'])).
% 0.20/0.50  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('96', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.50  thf('97', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['67', '96'])).
% 0.20/0.50  thf('98', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['97', '98'])).
% 0.20/0.50  thf('100', plain,
% 0.20/0.50      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['64'])).
% 0.20/0.50  thf('101', plain,
% 0.20/0.50      (~ ((r1_tsep_1 @ sk_C_2 @ sk_D)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.50  thf('102', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('103', plain,
% 0.20/0.50      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['64'])).
% 0.20/0.50  thf('104', plain,
% 0.20/0.50      (~ ((r1_tsep_1 @ sk_D @ sk_C_2)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.50  thf('105', plain,
% 0.20/0.50      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.50      inference('split', [status(esa)], ['64'])).
% 0.20/0.50  thf('106', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('107', plain,
% 0.20/0.50      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('108', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['97', '98'])).
% 0.20/0.50  thf('109', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X18)
% 0.20/0.50          | ~ (l1_struct_0 @ X19)
% 0.20/0.50          | (r1_tsep_1 @ X19 @ X18)
% 0.20/0.50          | ~ (r1_tsep_1 @ X18 @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.50  thf('110', plain,
% 0.20/0.50      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.50  thf('111', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['107', '110'])).
% 0.20/0.50  thf('112', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('113', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['111', '112'])).
% 0.20/0.50  thf('114', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['106', '113'])).
% 0.20/0.50  thf('115', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('116', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['114', '115'])).
% 0.20/0.50  thf('117', plain,
% 0.20/0.50      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['64'])).
% 0.20/0.50  thf('118', plain,
% 0.20/0.50      (~ ((r1_tsep_1 @ sk_C_2 @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['116', '117'])).
% 0.20/0.50  thf('119', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_C_2 @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C_2))),
% 0.20/0.50      inference('split', [status(esa)], ['6'])).
% 0.20/0.50  thf('120', plain, ($false),
% 0.20/0.50      inference('sat_resolution*', [status(thm)],
% 0.20/0.50                ['66', '101', '104', '105', '118', '119'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
