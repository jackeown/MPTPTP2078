%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nVEgxRtt1W

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:33 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  247 (1050 expanded)
%              Number of leaves         :   23 ( 300 expanded)
%              Depth                    :   25
%              Number of atoms          : 2707 (30940 expanded)
%              Number of equality atoms :   15 (  52 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(t40_tmap_1,conjecture,(
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
                 => ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                     => ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ C @ D ) ) )
                    & ( ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ C @ D ) )
                     => ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) )
                    & ( ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) )
                     => ( ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ D @ C ) ) )
                    & ( ( ( r1_tsep_1 @ D @ B )
                        & ( r1_tsep_1 @ D @ C ) )
                     => ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) )).

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
                   => ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D )
                       => ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ C @ D ) ) )
                      & ( ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ C @ D ) )
                       => ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) )
                      & ( ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) )
                       => ( ( r1_tsep_1 @ D @ B )
                          & ( r1_tsep_1 @ D @ C ) ) )
                      & ( ( ( r1_tsep_1 @ D @ B )
                          & ( r1_tsep_1 @ D @ C ) )
                       => ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_tmap_1])).

thf('0',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X14 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['13'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('16',plain,
    ( ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('23',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf('26',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['26'])).

thf('36',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('39',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('48',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['39','46','47'])).

thf('49',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['26'])).

thf('50',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v1_pre_topc @ ( k1_tsep_1 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_pre_topc @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( D
                      = ( k1_tsep_1 @ A @ B @ C ) )
                  <=> ( ( u1_struct_0 @ D )
                      = ( k2_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X9 )
      | ~ ( v1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( X9
       != ( k1_tsep_1 @ X8 @ X7 @ X10 ) )
      | ( ( u1_struct_0 @ X9 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('60',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X8 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) @ X8 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X8 @ X7 @ X10 ) )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( v2_struct_0 @ ( k1_tsep_1 @ X14 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('77',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['77'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('79',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_tsep_1 @ X12 @ X11 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('80',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('82',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('86',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('87',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['13'])).

thf('102',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('103',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('106',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('108',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('111',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf('112',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_tsep_1 @ X12 @ X11 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('115',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup+',[status(thm)],['109','117'])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('123',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('125',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('126',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['135'])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(simplify,[status(thm)],['118'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('139',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_C )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('143',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('149',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['141','142','149'])).

thf('151',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('152',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['147','148'])).

thf('154',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('155',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_C @ sk_D ) )
   <= ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['26'])).

thf('157',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
      & ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('165',plain,
    ( ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['77'])).

thf('166',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('167',plain,
    ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('169',plain,
    ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['164','169'])).

thf('171',plain,
    ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['26'])).

thf('172',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['77'])).

thf('180',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_tsep_1 @ X12 @ X11 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('181',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('183',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['147','148'])).

thf('184',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('186',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_tsep_1 @ X12 @ X11 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('187',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('189',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('190',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('192',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ X0 )
        | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['184','192'])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('195',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['74'])).

thf('196',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['194','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['193','199'])).

thf('201',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('202',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['26'])).

thf('204',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B )
      & ( r1_tsep_1 @ sk_D @ sk_C ) ) ),
    inference(clc,[status(thm)],['206','207'])).

thf('209',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['211'])).

thf('213',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('214',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('216',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['147','148'])).

thf('217',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['26'])).

thf('219',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k1_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['220'])).

thf('222',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['34','35','50','100','108','134','136','163','178','210','219','221'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nVEgxRtt1W
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.53/1.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.53/1.73  % Solved by: fo/fo7.sh
% 1.53/1.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.53/1.73  % done 1333 iterations in 1.276s
% 1.53/1.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.53/1.73  % SZS output start Refutation
% 1.53/1.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.53/1.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.53/1.73  thf(sk_D_type, type, sk_D: $i).
% 1.53/1.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.53/1.73  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.53/1.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.53/1.73  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 1.53/1.73  thf(sk_C_type, type, sk_C: $i).
% 1.53/1.73  thf(sk_B_type, type, sk_B: $i).
% 1.53/1.73  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 1.53/1.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.53/1.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.53/1.73  thf(sk_A_type, type, sk_A: $i).
% 1.53/1.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.53/1.73  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.53/1.73  thf(t40_tmap_1, conjecture,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.53/1.73       ( ![B:$i]:
% 1.53/1.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.53/1.73           ( ![C:$i]:
% 1.53/1.73             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.53/1.73               ( ![D:$i]:
% 1.53/1.73                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.53/1.73                   ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) =>
% 1.53/1.73                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 1.53/1.73                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) =>
% 1.53/1.73                       ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 1.53/1.73                     ( ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) =>
% 1.53/1.73                       ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 1.53/1.73                     ( ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) =>
% 1.53/1.73                       ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.53/1.73  thf(zf_stmt_0, negated_conjecture,
% 1.53/1.73    (~( ![A:$i]:
% 1.53/1.73        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.53/1.73            ( l1_pre_topc @ A ) ) =>
% 1.53/1.73          ( ![B:$i]:
% 1.53/1.73            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.53/1.73              ( ![C:$i]:
% 1.53/1.73                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.53/1.73                  ( ![D:$i]:
% 1.53/1.73                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.53/1.73                      ( ( ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) =>
% 1.53/1.73                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) ) & 
% 1.53/1.73                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ C @ D ) ) =>
% 1.53/1.73                          ( r1_tsep_1 @ ( k1_tsep_1 @ A @ B @ C ) @ D ) ) & 
% 1.53/1.73                        ( ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) =>
% 1.53/1.73                          ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) ) & 
% 1.53/1.73                        ( ( ( r1_tsep_1 @ D @ B ) & ( r1_tsep_1 @ D @ C ) ) =>
% 1.53/1.73                          ( r1_tsep_1 @ D @ ( k1_tsep_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) )),
% 1.53/1.73    inference('cnf.neg', [status(esa)], [t40_tmap_1])).
% 1.53/1.73  thf('0', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf(dt_k1_tsep_1, axiom,
% 1.53/1.73    (![A:$i,B:$i,C:$i]:
% 1.53/1.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.53/1.73         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.53/1.73         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.53/1.73       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 1.53/1.73         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 1.53/1.73         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.53/1.73  thf('2', plain,
% 1.53/1.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.53/1.73         (~ (m1_pre_topc @ X13 @ X14)
% 1.53/1.73          | (v2_struct_0 @ X13)
% 1.53/1.73          | ~ (l1_pre_topc @ X14)
% 1.53/1.73          | (v2_struct_0 @ X14)
% 1.53/1.73          | (v2_struct_0 @ X15)
% 1.53/1.73          | ~ (m1_pre_topc @ X15 @ X14)
% 1.53/1.73          | (m1_pre_topc @ (k1_tsep_1 @ X14 @ X13 @ X15) @ X14))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.53/1.73  thf('3', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.53/1.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ sk_A)
% 1.53/1.73          | ~ (l1_pre_topc @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ sk_B))),
% 1.53/1.73      inference('sup-', [status(thm)], ['1', '2'])).
% 1.53/1.73  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('5', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.53/1.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ sk_B))),
% 1.53/1.73      inference('demod', [status(thm)], ['3', '4'])).
% 1.53/1.73  thf('6', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.53/1.73      inference('sup-', [status(thm)], ['0', '5'])).
% 1.53/1.73  thf(dt_m1_pre_topc, axiom,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( l1_pre_topc @ A ) =>
% 1.53/1.73       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.53/1.73  thf('7', plain,
% 1.53/1.73      (![X5 : $i, X6 : $i]:
% 1.53/1.73         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.53/1.73  thf('8', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | ~ (l1_pre_topc @ sk_A)
% 1.53/1.73        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['6', '7'])).
% 1.53/1.73  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('10', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (l1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('demod', [status(thm)], ['8', '9'])).
% 1.53/1.73  thf(dt_l1_pre_topc, axiom,
% 1.53/1.73    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.53/1.73  thf('11', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.53/1.73  thf('12', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['10', '11'])).
% 1.53/1.73  thf('13', plain,
% 1.53/1.73      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.53/1.73        | (r1_tsep_1 @ sk_B @ sk_D)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_D @ sk_C)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('14', plain,
% 1.53/1.73      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('split', [status(esa)], ['13'])).
% 1.53/1.73  thf(symmetry_r1_tsep_1, axiom,
% 1.53/1.73    (![A:$i,B:$i]:
% 1.53/1.73     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 1.53/1.73       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 1.53/1.73  thf('15', plain,
% 1.53/1.73      (![X16 : $i, X17 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X16)
% 1.53/1.73          | ~ (l1_struct_0 @ X17)
% 1.53/1.73          | (r1_tsep_1 @ X17 @ X16)
% 1.53/1.73          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.53/1.73      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.53/1.73  thf('16', plain,
% 1.53/1.73      ((((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D)
% 1.53/1.73         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['14', '15'])).
% 1.53/1.73  thf('17', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('18', plain,
% 1.53/1.73      (![X5 : $i, X6 : $i]:
% 1.53/1.73         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.53/1.73  thf('19', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.53/1.73      inference('sup-', [status(thm)], ['17', '18'])).
% 1.53/1.73  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('21', plain, ((l1_pre_topc @ sk_D)),
% 1.53/1.73      inference('demod', [status(thm)], ['19', '20'])).
% 1.53/1.73  thf('22', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.53/1.73  thf('23', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('24', plain,
% 1.53/1.73      ((((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('demod', [status(thm)], ['16', '23'])).
% 1.53/1.73  thf('25', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['12', '24'])).
% 1.53/1.73  thf('26', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_C @ sk_D)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 1.53/1.73        | ~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_D @ sk_C)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('27', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('split', [status(esa)], ['26'])).
% 1.53/1.73  thf('28', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.53/1.73             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['25', '27'])).
% 1.53/1.73  thf('29', plain, (~ (v2_struct_0 @ sk_B)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('30', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.53/1.73             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('clc', [status(thm)], ['28', '29'])).
% 1.53/1.73  thf('31', plain, (~ (v2_struct_0 @ sk_C)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('32', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_A))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.53/1.73             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('clc', [status(thm)], ['30', '31'])).
% 1.53/1.73  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('34', plain,
% 1.53/1.73      (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 1.53/1.73       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['32', '33'])).
% 1.53/1.73  thf('35', plain,
% 1.53/1.73      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.53/1.73       ~ ((r1_tsep_1 @ sk_D @ sk_C)) | 
% 1.53/1.73       ~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 1.53/1.73       ~ ((r1_tsep_1 @ sk_C @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_B)) | 
% 1.53/1.73       ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 1.53/1.73      inference('split', [status(esa)], ['26'])).
% 1.53/1.73  thf('36', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_C @ sk_D)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 1.53/1.73        | ~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.53/1.73        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | (r1_tsep_1 @ sk_D @ sk_B))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('37', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.53/1.73      inference('split', [status(esa)], ['36'])).
% 1.53/1.73  thf('38', plain,
% 1.53/1.73      (![X16 : $i, X17 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X16)
% 1.53/1.73          | ~ (l1_struct_0 @ X17)
% 1.53/1.73          | (r1_tsep_1 @ X17 @ X16)
% 1.53/1.73          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.53/1.73      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.53/1.73  thf('39', plain,
% 1.53/1.73      ((((r1_tsep_1 @ sk_B @ sk_D)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_B)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['37', '38'])).
% 1.53/1.73  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('41', plain,
% 1.53/1.73      (![X5 : $i, X6 : $i]:
% 1.53/1.73         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.53/1.73  thf('42', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.53/1.73      inference('sup-', [status(thm)], ['40', '41'])).
% 1.53/1.73  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 1.53/1.73      inference('demod', [status(thm)], ['42', '43'])).
% 1.53/1.73  thf('45', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.53/1.73  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.73      inference('sup-', [status(thm)], ['44', '45'])).
% 1.53/1.73  thf('47', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('48', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.53/1.73      inference('demod', [status(thm)], ['39', '46', '47'])).
% 1.53/1.73  thf('49', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.53/1.73      inference('split', [status(esa)], ['26'])).
% 1.53/1.73  thf('50', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 1.53/1.73      inference('sup-', [status(thm)], ['48', '49'])).
% 1.53/1.73  thf('51', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('52', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('53', plain,
% 1.53/1.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.53/1.73         (~ (m1_pre_topc @ X13 @ X14)
% 1.53/1.73          | (v2_struct_0 @ X13)
% 1.53/1.73          | ~ (l1_pre_topc @ X14)
% 1.53/1.73          | (v2_struct_0 @ X14)
% 1.53/1.73          | (v2_struct_0 @ X15)
% 1.53/1.73          | ~ (m1_pre_topc @ X15 @ X14)
% 1.53/1.73          | (v1_pre_topc @ (k1_tsep_1 @ X14 @ X13 @ X15)))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.53/1.73  thf('54', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.53/1.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ sk_A)
% 1.53/1.73          | ~ (l1_pre_topc @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ sk_B))),
% 1.53/1.73      inference('sup-', [status(thm)], ['52', '53'])).
% 1.53/1.73  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('56', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ X0))
% 1.53/1.73          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ sk_B))),
% 1.53/1.73      inference('demod', [status(thm)], ['54', '55'])).
% 1.53/1.73  thf('57', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['51', '56'])).
% 1.53/1.73  thf('58', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.53/1.73      inference('sup-', [status(thm)], ['0', '5'])).
% 1.53/1.73  thf(d2_tsep_1, axiom,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.53/1.73       ( ![B:$i]:
% 1.53/1.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.53/1.73           ( ![C:$i]:
% 1.53/1.73             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.53/1.73               ( ![D:$i]:
% 1.53/1.73                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 1.53/1.73                     ( m1_pre_topc @ D @ A ) ) =>
% 1.53/1.73                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 1.53/1.73                     ( ( u1_struct_0 @ D ) =
% 1.53/1.73                       ( k2_xboole_0 @
% 1.53/1.73                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.53/1.73  thf('59', plain,
% 1.53/1.73      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.53/1.73         ((v2_struct_0 @ X7)
% 1.53/1.73          | ~ (m1_pre_topc @ X7 @ X8)
% 1.53/1.73          | (v2_struct_0 @ X9)
% 1.53/1.73          | ~ (v1_pre_topc @ X9)
% 1.53/1.73          | ~ (m1_pre_topc @ X9 @ X8)
% 1.53/1.73          | ((X9) != (k1_tsep_1 @ X8 @ X7 @ X10))
% 1.53/1.73          | ((u1_struct_0 @ X9)
% 1.53/1.73              = (k2_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X10)))
% 1.53/1.73          | ~ (m1_pre_topc @ X10 @ X8)
% 1.53/1.73          | (v2_struct_0 @ X10)
% 1.53/1.73          | ~ (l1_pre_topc @ X8)
% 1.53/1.73          | (v2_struct_0 @ X8))),
% 1.53/1.73      inference('cnf', [status(esa)], [d2_tsep_1])).
% 1.53/1.73  thf('60', plain,
% 1.53/1.73      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.53/1.73         ((v2_struct_0 @ X8)
% 1.53/1.73          | ~ (l1_pre_topc @ X8)
% 1.53/1.73          | (v2_struct_0 @ X10)
% 1.53/1.73          | ~ (m1_pre_topc @ X10 @ X8)
% 1.53/1.73          | ((u1_struct_0 @ (k1_tsep_1 @ X8 @ X7 @ X10))
% 1.53/1.73              = (k2_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X10)))
% 1.53/1.73          | ~ (m1_pre_topc @ (k1_tsep_1 @ X8 @ X7 @ X10) @ X8)
% 1.53/1.73          | ~ (v1_pre_topc @ (k1_tsep_1 @ X8 @ X7 @ X10))
% 1.53/1.73          | (v2_struct_0 @ (k1_tsep_1 @ X8 @ X7 @ X10))
% 1.53/1.73          | ~ (m1_pre_topc @ X7 @ X8)
% 1.53/1.73          | (v2_struct_0 @ X7))),
% 1.53/1.73      inference('simplify', [status(thm)], ['59'])).
% 1.53/1.73  thf('61', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | ~ (l1_pre_topc @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_A))),
% 1.53/1.73      inference('sup-', [status(thm)], ['58', '60'])).
% 1.53/1.73  thf('62', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('63', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('65', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A))),
% 1.53/1.73      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 1.53/1.73  thf('66', plain,
% 1.53/1.73      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C))),
% 1.53/1.73      inference('simplify', [status(thm)], ['65'])).
% 1.53/1.73  thf('67', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['57', '66'])).
% 1.53/1.73  thf('68', plain,
% 1.53/1.73      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73        | (v2_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C))),
% 1.53/1.73      inference('simplify', [status(thm)], ['67'])).
% 1.53/1.73  thf('69', plain,
% 1.53/1.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.53/1.73         (~ (m1_pre_topc @ X13 @ X14)
% 1.53/1.73          | (v2_struct_0 @ X13)
% 1.53/1.73          | ~ (l1_pre_topc @ X14)
% 1.53/1.73          | (v2_struct_0 @ X14)
% 1.53/1.73          | (v2_struct_0 @ X15)
% 1.53/1.73          | ~ (m1_pre_topc @ X15 @ X14)
% 1.53/1.73          | ~ (v2_struct_0 @ (k1_tsep_1 @ X14 @ X13 @ X15)))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 1.53/1.73  thf('70', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | ~ (l1_pre_topc @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 1.53/1.73      inference('sup-', [status(thm)], ['68', '69'])).
% 1.53/1.73  thf('71', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('73', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('74', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | ((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_B))),
% 1.53/1.73      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 1.53/1.73  thf('75', plain,
% 1.53/1.73      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C))),
% 1.53/1.73      inference('simplify', [status(thm)], ['74'])).
% 1.53/1.73  thf('76', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['10', '11'])).
% 1.53/1.73  thf('77', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_C @ sk_D)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_B @ sk_D)
% 1.53/1.73        | ~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.53/1.73        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | (r1_tsep_1 @ sk_D @ sk_C))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('78', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('split', [status(esa)], ['77'])).
% 1.53/1.73  thf(d3_tsep_1, axiom,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( l1_struct_0 @ A ) =>
% 1.53/1.73       ( ![B:$i]:
% 1.53/1.73         ( ( l1_struct_0 @ B ) =>
% 1.53/1.73           ( ( r1_tsep_1 @ A @ B ) <=>
% 1.53/1.73             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.53/1.73  thf('79', plain,
% 1.53/1.73      (![X11 : $i, X12 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X11)
% 1.53/1.73          | ~ (r1_tsep_1 @ X12 @ X11)
% 1.53/1.73          | (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.53/1.73          | ~ (l1_struct_0 @ X12))),
% 1.53/1.73      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.53/1.73  thf('80', plain,
% 1.53/1.73      (((~ (l1_struct_0 @ sk_D)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.53/1.73         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['78', '79'])).
% 1.53/1.73  thf('81', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('82', plain,
% 1.53/1.73      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73          (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.53/1.73         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('demod', [status(thm)], ['80', '81'])).
% 1.53/1.73  thf('83', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['76', '82'])).
% 1.53/1.73  thf('84', plain,
% 1.53/1.73      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73          (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('sup+', [status(thm)], ['75', '83'])).
% 1.53/1.73  thf('85', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73            (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('simplify', [status(thm)], ['84'])).
% 1.53/1.73  thf(t70_xboole_1, axiom,
% 1.53/1.73    (![A:$i,B:$i,C:$i]:
% 1.53/1.73     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.53/1.73            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.53/1.73       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.53/1.73            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.53/1.73  thf('86', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.53/1.73         ((r1_xboole_0 @ X0 @ X1)
% 1.53/1.73          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X3)))),
% 1.53/1.73      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.53/1.73  thf('87', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['85', '86'])).
% 1.53/1.73  thf('88', plain,
% 1.53/1.73      (![X11 : $i, X12 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X11)
% 1.53/1.73          | ~ (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.53/1.73          | (r1_tsep_1 @ X12 @ X11)
% 1.53/1.73          | ~ (l1_struct_0 @ X12))),
% 1.53/1.73      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.53/1.73  thf('89', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D)
% 1.53/1.73         | (r1_tsep_1 @ sk_D @ sk_B)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_B)))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['87', '88'])).
% 1.53/1.73  thf('90', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.73      inference('sup-', [status(thm)], ['44', '45'])).
% 1.53/1.73  thf('92', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (r1_tsep_1 @ sk_D @ sk_B)))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.53/1.73  thf('93', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.53/1.73      inference('split', [status(esa)], ['26'])).
% 1.53/1.73  thf('94', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['92', '93'])).
% 1.53/1.73  thf('95', plain, (~ (v2_struct_0 @ sk_C)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('96', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('clc', [status(thm)], ['94', '95'])).
% 1.53/1.73  thf('97', plain, (~ (v2_struct_0 @ sk_B)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('98', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_A))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('clc', [status(thm)], ['96', '97'])).
% 1.53/1.73  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('100', plain,
% 1.53/1.73      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.53/1.73       ((r1_tsep_1 @ sk_D @ sk_B))),
% 1.53/1.73      inference('sup-', [status(thm)], ['98', '99'])).
% 1.53/1.73  thf('101', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.53/1.73      inference('split', [status(esa)], ['13'])).
% 1.53/1.73  thf('102', plain,
% 1.53/1.73      (![X16 : $i, X17 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X16)
% 1.53/1.73          | ~ (l1_struct_0 @ X17)
% 1.53/1.73          | (r1_tsep_1 @ X17 @ X16)
% 1.53/1.73          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.53/1.73      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.53/1.73  thf('103', plain,
% 1.53/1.73      ((((r1_tsep_1 @ sk_D @ sk_B)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['101', '102'])).
% 1.53/1.73  thf('104', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.73      inference('sup-', [status(thm)], ['44', '45'])).
% 1.53/1.73  thf('106', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.53/1.73      inference('demod', [status(thm)], ['103', '104', '105'])).
% 1.53/1.73  thf('107', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.53/1.73      inference('split', [status(esa)], ['26'])).
% 1.53/1.73  thf('108', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 1.53/1.73      inference('sup-', [status(thm)], ['106', '107'])).
% 1.53/1.73  thf('109', plain,
% 1.53/1.73      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C))),
% 1.53/1.73      inference('simplify', [status(thm)], ['74'])).
% 1.53/1.73  thf('110', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['10', '11'])).
% 1.53/1.73  thf('111', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['12', '24'])).
% 1.53/1.73  thf('112', plain,
% 1.53/1.73      (![X11 : $i, X12 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X11)
% 1.53/1.73          | ~ (r1_tsep_1 @ X12 @ X11)
% 1.53/1.73          | (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.53/1.73          | ~ (l1_struct_0 @ X12))),
% 1.53/1.73      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.53/1.73  thf('113', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.53/1.73         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['111', '112'])).
% 1.53/1.73  thf('114', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('115', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.53/1.73         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('demod', [status(thm)], ['113', '114'])).
% 1.53/1.73  thf('116', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73            (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['110', '115'])).
% 1.53/1.73  thf('117', plain,
% 1.53/1.73      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73          (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('simplify', [status(thm)], ['116'])).
% 1.53/1.73  thf('118', plain,
% 1.53/1.73      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73          (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup+', [status(thm)], ['109', '117'])).
% 1.53/1.73  thf('119', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73            (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('simplify', [status(thm)], ['118'])).
% 1.53/1.73  thf('120', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.53/1.73         ((r1_xboole_0 @ X0 @ X1)
% 1.53/1.73          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X3)))),
% 1.53/1.73      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.53/1.73  thf('121', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['119', '120'])).
% 1.53/1.73  thf('122', plain,
% 1.53/1.73      (![X11 : $i, X12 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X11)
% 1.53/1.73          | ~ (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.53/1.73          | (r1_tsep_1 @ X12 @ X11)
% 1.53/1.73          | ~ (l1_struct_0 @ X12))),
% 1.53/1.73      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.53/1.73  thf('123', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D)
% 1.53/1.73         | (r1_tsep_1 @ sk_D @ sk_B)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_B)))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['121', '122'])).
% 1.53/1.73  thf('124', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('125', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.73      inference('sup-', [status(thm)], ['44', '45'])).
% 1.53/1.73  thf('126', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (r1_tsep_1 @ sk_D @ sk_B)))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('demod', [status(thm)], ['123', '124', '125'])).
% 1.53/1.73  thf('127', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.53/1.73      inference('split', [status(esa)], ['26'])).
% 1.53/1.73  thf('128', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_B)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.53/1.73             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['126', '127'])).
% 1.53/1.73  thf('129', plain, (~ (v2_struct_0 @ sk_C)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('130', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.53/1.73             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('clc', [status(thm)], ['128', '129'])).
% 1.53/1.73  thf('131', plain, (~ (v2_struct_0 @ sk_B)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('132', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_A))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.53/1.73             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('clc', [status(thm)], ['130', '131'])).
% 1.53/1.73  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('134', plain,
% 1.53/1.73      (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 1.53/1.73       ((r1_tsep_1 @ sk_D @ sk_B))),
% 1.53/1.73      inference('sup-', [status(thm)], ['132', '133'])).
% 1.53/1.73  thf('135', plain,
% 1.53/1.73      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.53/1.73        | (r1_tsep_1 @ sk_B @ sk_D)
% 1.53/1.73        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | (r1_tsep_1 @ sk_D @ sk_B))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('136', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_D @ sk_B)) | 
% 1.53/1.73       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.53/1.73       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 1.53/1.73       ((r1_tsep_1 @ sk_B @ sk_D))),
% 1.53/1.73      inference('split', [status(esa)], ['135'])).
% 1.53/1.73  thf('137', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73            (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('simplify', [status(thm)], ['118'])).
% 1.53/1.73  thf('138', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i, X3 : $i]:
% 1.53/1.73         ((r1_xboole_0 @ X0 @ X3)
% 1.53/1.73          | ~ (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X3)))),
% 1.53/1.73      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.53/1.73  thf('139', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['137', '138'])).
% 1.53/1.73  thf('140', plain,
% 1.53/1.73      (![X11 : $i, X12 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X11)
% 1.53/1.73          | ~ (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.53/1.73          | (r1_tsep_1 @ X12 @ X11)
% 1.53/1.73          | ~ (l1_struct_0 @ X12))),
% 1.53/1.73      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.53/1.73  thf('141', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D)
% 1.53/1.73         | (r1_tsep_1 @ sk_D @ sk_C)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_C)))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['139', '140'])).
% 1.53/1.73  thf('142', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('143', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('144', plain,
% 1.53/1.73      (![X5 : $i, X6 : $i]:
% 1.53/1.73         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.53/1.73  thf('145', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.53/1.73      inference('sup-', [status(thm)], ['143', '144'])).
% 1.53/1.73  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('147', plain, ((l1_pre_topc @ sk_C)),
% 1.53/1.73      inference('demod', [status(thm)], ['145', '146'])).
% 1.53/1.73  thf('148', plain, (![X4 : $i]: ((l1_struct_0 @ X4) | ~ (l1_pre_topc @ X4))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.53/1.73  thf('149', plain, ((l1_struct_0 @ sk_C)),
% 1.53/1.73      inference('sup-', [status(thm)], ['147', '148'])).
% 1.53/1.73  thf('150', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_C)
% 1.53/1.73         | (r1_tsep_1 @ sk_D @ sk_C)))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('demod', [status(thm)], ['141', '142', '149'])).
% 1.53/1.73  thf('151', plain,
% 1.53/1.73      (![X16 : $i, X17 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X16)
% 1.53/1.73          | ~ (l1_struct_0 @ X17)
% 1.53/1.73          | (r1_tsep_1 @ X17 @ X16)
% 1.53/1.73          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.53/1.73      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.53/1.73  thf('152', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_tsep_1 @ sk_C @ sk_D)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_C)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D)))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['150', '151'])).
% 1.53/1.73  thf('153', plain, ((l1_struct_0 @ sk_C)),
% 1.53/1.73      inference('sup-', [status(thm)], ['147', '148'])).
% 1.53/1.73  thf('154', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('155', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_tsep_1 @ sk_C @ sk_D)))
% 1.53/1.73         <= (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.53/1.73  thf('156', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_C @ sk_D)) <= (~ ((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.53/1.73      inference('split', [status(esa)], ['26'])).
% 1.53/1.73  thf('157', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_C @ sk_D)) & 
% 1.53/1.73             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['155', '156'])).
% 1.53/1.73  thf('158', plain, (~ (v2_struct_0 @ sk_B)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('159', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_C @ sk_D)) & 
% 1.53/1.73             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('clc', [status(thm)], ['157', '158'])).
% 1.53/1.73  thf('160', plain, (~ (v2_struct_0 @ sk_C)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('161', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_A))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_C @ sk_D)) & 
% 1.53/1.73             ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('clc', [status(thm)], ['159', '160'])).
% 1.53/1.73  thf('162', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('163', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_C @ sk_D)) | 
% 1.53/1.73       ~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 1.53/1.73      inference('sup-', [status(thm)], ['161', '162'])).
% 1.53/1.73  thf('164', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['10', '11'])).
% 1.53/1.73  thf('165', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('split', [status(esa)], ['77'])).
% 1.53/1.73  thf('166', plain,
% 1.53/1.73      (![X16 : $i, X17 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X16)
% 1.53/1.73          | ~ (l1_struct_0 @ X17)
% 1.53/1.73          | (r1_tsep_1 @ X17 @ X16)
% 1.53/1.73          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.53/1.73      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.53/1.73  thf('167', plain,
% 1.53/1.73      ((((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.53/1.73         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D)))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['165', '166'])).
% 1.53/1.73  thf('168', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('169', plain,
% 1.53/1.73      ((((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.53/1.73         | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('demod', [status(thm)], ['167', '168'])).
% 1.53/1.73  thf('170', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['164', '169'])).
% 1.53/1.73  thf('171', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.53/1.73      inference('split', [status(esa)], ['26'])).
% 1.53/1.73  thf('172', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['170', '171'])).
% 1.53/1.73  thf('173', plain, (~ (v2_struct_0 @ sk_B)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('174', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('clc', [status(thm)], ['172', '173'])).
% 1.53/1.73  thf('175', plain, (~ (v2_struct_0 @ sk_C)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('176', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_A))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('clc', [status(thm)], ['174', '175'])).
% 1.53/1.73  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('178', plain,
% 1.53/1.73      (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.53/1.73       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 1.53/1.73      inference('sup-', [status(thm)], ['176', '177'])).
% 1.53/1.73  thf('179', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.53/1.73      inference('split', [status(esa)], ['77'])).
% 1.53/1.73  thf('180', plain,
% 1.53/1.73      (![X11 : $i, X12 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X11)
% 1.53/1.73          | ~ (r1_tsep_1 @ X12 @ X11)
% 1.53/1.73          | (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.53/1.73          | ~ (l1_struct_0 @ X12))),
% 1.53/1.73      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.53/1.73  thf('181', plain,
% 1.53/1.73      (((~ (l1_struct_0 @ sk_D)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 1.53/1.73         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['179', '180'])).
% 1.53/1.73  thf('182', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('183', plain, ((l1_struct_0 @ sk_C)),
% 1.53/1.73      inference('sup-', [status(thm)], ['147', '148'])).
% 1.53/1.73  thf('184', plain,
% 1.53/1.73      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.53/1.73      inference('demod', [status(thm)], ['181', '182', '183'])).
% 1.53/1.73  thf('185', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.53/1.73      inference('split', [status(esa)], ['36'])).
% 1.53/1.73  thf('186', plain,
% 1.53/1.73      (![X11 : $i, X12 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X11)
% 1.53/1.73          | ~ (r1_tsep_1 @ X12 @ X11)
% 1.53/1.73          | (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.53/1.73          | ~ (l1_struct_0 @ X12))),
% 1.53/1.73      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.53/1.73  thf('187', plain,
% 1.53/1.73      (((~ (l1_struct_0 @ sk_D)
% 1.53/1.73         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 1.53/1.73         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['185', '186'])).
% 1.53/1.73  thf('188', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('189', plain, ((l1_struct_0 @ sk_B)),
% 1.53/1.73      inference('sup-', [status(thm)], ['44', '45'])).
% 1.53/1.73  thf('190', plain,
% 1.53/1.73      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.53/1.73      inference('demod', [status(thm)], ['187', '188', '189'])).
% 1.53/1.73  thf('191', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.73         ((r1_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2))
% 1.53/1.73          | ~ (r1_xboole_0 @ X0 @ X1)
% 1.53/1.73          | ~ (r1_xboole_0 @ X0 @ X2))),
% 1.53/1.73      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.53/1.73  thf('192', plain,
% 1.53/1.73      ((![X0 : $i]:
% 1.53/1.73          (~ (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ X0)
% 1.53/1.73           | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73              (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['190', '191'])).
% 1.53/1.73  thf('193', plain,
% 1.53/1.73      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ 
% 1.53/1.73         (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ sk_B)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['184', '192'])).
% 1.53/1.73  thf('194', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C)
% 1.53/1.73        | (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['10', '11'])).
% 1.53/1.73  thf('195', plain,
% 1.53/1.73      ((((u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73          = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73        | (v2_struct_0 @ sk_B)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_C))),
% 1.53/1.73      inference('simplify', [status(thm)], ['74'])).
% 1.53/1.73  thf('196', plain,
% 1.53/1.73      (![X11 : $i, X12 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X11)
% 1.53/1.73          | ~ (r1_xboole_0 @ (u1_struct_0 @ X12) @ (u1_struct_0 @ X11))
% 1.53/1.73          | (r1_tsep_1 @ X12 @ X11)
% 1.53/1.73          | ~ (l1_struct_0 @ X12))),
% 1.53/1.73      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.53/1.73  thf('197', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 1.53/1.73             (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73          | (v2_struct_0 @ sk_C)
% 1.53/1.73          | (v2_struct_0 @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ sk_B)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (r1_tsep_1 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73          | ~ (l1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['195', '196'])).
% 1.53/1.73  thf('198', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((v2_struct_0 @ sk_C)
% 1.53/1.73          | (v2_struct_0 @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ sk_B)
% 1.53/1.73          | (r1_tsep_1 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ sk_B)
% 1.53/1.73          | (v2_struct_0 @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ sk_C)
% 1.53/1.73          | ~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 1.53/1.73               (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['194', '197'])).
% 1.53/1.73  thf('199', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (r1_xboole_0 @ (u1_struct_0 @ X0) @ 
% 1.53/1.73             (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (r1_tsep_1 @ X0 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73          | (v2_struct_0 @ sk_B)
% 1.53/1.73          | (v2_struct_0 @ sk_A)
% 1.53/1.73          | (v2_struct_0 @ sk_C))),
% 1.53/1.73      inference('simplify', [status(thm)], ['198'])).
% 1.53/1.73  thf('200', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D)))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ sk_B)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['193', '199'])).
% 1.53/1.73  thf('201', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('202', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C)
% 1.53/1.73         | (v2_struct_0 @ sk_A)
% 1.53/1.73         | (v2_struct_0 @ sk_B)
% 1.53/1.73         | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.53/1.73         <= (((r1_tsep_1 @ sk_D @ sk_B)) & ((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.53/1.73      inference('demod', [status(thm)], ['200', '201'])).
% 1.53/1.73  thf('203', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.53/1.73      inference('split', [status(esa)], ['26'])).
% 1.53/1.73  thf('204', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['202', '203'])).
% 1.53/1.73  thf('205', plain, (~ (v2_struct_0 @ sk_B)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('206', plain,
% 1.53/1.73      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.53/1.73      inference('clc', [status(thm)], ['204', '205'])).
% 1.53/1.73  thf('207', plain, (~ (v2_struct_0 @ sk_C)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('208', plain,
% 1.53/1.73      (((v2_struct_0 @ sk_A))
% 1.53/1.73         <= (~ ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ sk_B)) & 
% 1.53/1.73             ((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.53/1.73      inference('clc', [status(thm)], ['206', '207'])).
% 1.53/1.73  thf('209', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('210', plain,
% 1.53/1.73      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | 
% 1.53/1.73       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.53/1.73       ~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 1.53/1.73      inference('sup-', [status(thm)], ['208', '209'])).
% 1.53/1.73  thf('211', plain,
% 1.53/1.73      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.53/1.73        | (r1_tsep_1 @ sk_C @ sk_D)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_D @ sk_C)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_D @ sk_B)
% 1.53/1.73        | ~ (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('212', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.53/1.73      inference('split', [status(esa)], ['211'])).
% 1.53/1.73  thf('213', plain,
% 1.53/1.73      (![X16 : $i, X17 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X16)
% 1.53/1.73          | ~ (l1_struct_0 @ X17)
% 1.53/1.73          | (r1_tsep_1 @ X17 @ X16)
% 1.53/1.73          | ~ (r1_tsep_1 @ X16 @ X17))),
% 1.53/1.73      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.53/1.73  thf('214', plain,
% 1.53/1.73      ((((r1_tsep_1 @ sk_D @ sk_C)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_D)
% 1.53/1.73         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['212', '213'])).
% 1.53/1.73  thf('215', plain, ((l1_struct_0 @ sk_D)),
% 1.53/1.73      inference('sup-', [status(thm)], ['21', '22'])).
% 1.53/1.73  thf('216', plain, ((l1_struct_0 @ sk_C)),
% 1.53/1.73      inference('sup-', [status(thm)], ['147', '148'])).
% 1.53/1.73  thf('217', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.53/1.73      inference('demod', [status(thm)], ['214', '215', '216'])).
% 1.53/1.73  thf('218', plain,
% 1.53/1.73      ((~ (r1_tsep_1 @ sk_D @ sk_C)) <= (~ ((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.53/1.73      inference('split', [status(esa)], ['26'])).
% 1.53/1.73  thf('219', plain,
% 1.53/1.73      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C))),
% 1.53/1.73      inference('sup-', [status(thm)], ['217', '218'])).
% 1.53/1.73  thf('220', plain,
% 1.53/1.73      (((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.53/1.73        | (r1_tsep_1 @ sk_C @ sk_D)
% 1.53/1.73        | (r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.53/1.73        | (r1_tsep_1 @ sk_D @ sk_C))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('221', plain,
% 1.53/1.73      (((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C)) | 
% 1.53/1.73       ((r1_tsep_1 @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 1.53/1.73       ((r1_tsep_1 @ sk_D @ (k1_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.53/1.73      inference('split', [status(esa)], ['220'])).
% 1.53/1.73  thf('222', plain, ($false),
% 1.53/1.73      inference('sat_resolution*', [status(thm)],
% 1.53/1.73                ['34', '35', '50', '100', '108', '134', '136', '163', '178', 
% 1.53/1.73                 '210', '219', '221'])).
% 1.53/1.73  
% 1.53/1.73  % SZS output end Refutation
% 1.53/1.73  
% 1.53/1.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
