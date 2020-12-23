%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sQP7HhfNaQ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 788 expanded)
%              Number of leaves         :   21 ( 230 expanded)
%              Depth                    :   27
%              Number of atoms          :  891 (11645 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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

thf(t24_tmap_1,conjecture,(
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
                   => ( ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) )
                      | ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) )).

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
                     => ( ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) )
                        | ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tmap_1])).

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

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('33',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( r1_tarski @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('51',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['3','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('54',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','54'])).

thf('56',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('63',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['55','60'])).

thf('65',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('70',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('71',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('72',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('73',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_tsep_1 @ X13 @ X12 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('74',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('77',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('80',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('82',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('84',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['69','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('87',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['68','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('90',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['65'])).

thf('92',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['65'])).

thf('94',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('95',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('96',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('97',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('98',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('101',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['94','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('104',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['65'])).

thf('106',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('108',plain,(
    r1_tsep_1 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['67','92','93','106','107'])).

thf('109',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['63','108'])).

thf('110',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['1','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['58','59'])).

thf('112',plain,
    ( ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['65'])).

thf('114',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['67','92','107','93'])).

thf('115',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( l1_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['112','115'])).

thf('117',plain,(
    ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['0','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['117','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sQP7HhfNaQ
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 88 iterations in 0.035s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.49  thf(dt_l1_pre_topc, axiom,
% 0.19/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.49  thf('0', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('1', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('2', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('3', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('4', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('5', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('6', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('7', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf(t24_tmap_1, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.49               ( ![D:$i]:
% 0.19/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.49                   ( ( m1_pre_topc @ B @ C ) =>
% 0.19/0.49                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.19/0.49                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.19/0.49                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.49            ( l1_pre_topc @ A ) ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.49              ( ![C:$i]:
% 0.19/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.49                  ( ![D:$i]:
% 0.19/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.19/0.49                      ( ( m1_pre_topc @ B @ C ) =>
% 0.19/0.49                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.19/0.49                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.19/0.49                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.19/0.49  thf('8', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('split', [status(esa)], ['8'])).
% 0.19/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.19/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X14)
% 0.19/0.49          | ~ (l1_struct_0 @ X15)
% 0.19/0.49          | (r1_tsep_1 @ X15 @ X14)
% 0.19/0.49          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((((r1_tsep_1 @ sk_D @ sk_C)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.19/0.49         | (r1_tsep_1 @ sk_D @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['7', '11'])).
% 0.19/0.49  thf('13', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_m1_pre_topc, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.19/0.49          | (l1_pre_topc @ X10)
% 0.19/0.49          | ~ (l1_pre_topc @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.49  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['12', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '18'])).
% 0.19/0.49  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.19/0.49          | (l1_pre_topc @ X10)
% 0.19/0.49          | ~ (l1_pre_topc @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.49  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('24', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['19', '24'])).
% 0.19/0.49  thf(d3_tsep_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_struct_0 @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( l1_struct_0 @ B ) =>
% 0.19/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.19/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X12)
% 0.19/0.49          | ~ (r1_tsep_1 @ X13 @ X12)
% 0.19/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.19/0.49          | ~ (l1_struct_0 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '27'])).
% 0.19/0.49  thf('29', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '30'])).
% 0.19/0.49  thf('32', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.49  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t4_tsep_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.49               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.19/0.49                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X16 @ X17)
% 0.19/0.49          | ~ (m1_pre_topc @ X16 @ X18)
% 0.19/0.49          | (r1_tarski @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X18))
% 0.19/0.49          | ~ (m1_pre_topc @ X18 @ X17)
% 0.19/0.49          | ~ (l1_pre_topc @ X17)
% 0.19/0.49          | ~ (v2_pre_topc @ X17))),
% 0.19/0.49      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v2_pre_topc @ sk_A)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.49          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.19/0.49          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.49  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.19/0.49          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.19/0.49          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 0.19/0.49        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['34', '40'])).
% 0.19/0.49  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('43', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf(d10_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('45', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.19/0.49  thf(t64_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.19/0.49         ( r1_xboole_0 @ B @ D ) ) =>
% 0.19/0.49       ( r1_xboole_0 @ A @ C ) ))).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X3 @ X4)
% 0.19/0.49          | ~ (r1_tarski @ X3 @ X5)
% 0.19/0.49          | ~ (r1_tarski @ X4 @ X6)
% 0.19/0.49          | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.19/0.49      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r1_xboole_0 @ X0 @ X1)
% 0.19/0.49          | ~ (r1_tarski @ X2 @ X1)
% 0.19/0.49          | (r1_xboole_0 @ X0 @ X2))),
% 0.19/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B))
% 0.19/0.49          | ~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['43', '47'])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['33', '48'])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X12)
% 0.19/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.19/0.49          | (r1_tsep_1 @ X13 @ X12)
% 0.19/0.49          | ~ (l1_struct_0 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.19/0.49         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '51'])).
% 0.19/0.49  thf('53', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('54', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['52', '53'])).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '54'])).
% 0.19/0.49  thf('56', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('57', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X10 @ X11)
% 0.19/0.49          | (l1_pre_topc @ X10)
% 0.19/0.49          | ~ (l1_pre_topc @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.49  thf('58', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.19/0.49  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.49  thf('61', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['55', '60'])).
% 0.19/0.49  thf('62', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X14)
% 0.19/0.49          | ~ (l1_struct_0 @ X15)
% 0.19/0.49          | (r1_tsep_1 @ X15 @ X14)
% 0.19/0.49          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.19/0.49  thf('63', plain,
% 0.19/0.49      ((((r1_tsep_1 @ sk_B @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['61', '62'])).
% 0.19/0.49  thf('64', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['55', '60'])).
% 0.19/0.49  thf('65', plain,
% 0.19/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('66', plain,
% 0.19/0.49      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['65'])).
% 0.19/0.49  thf('67', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['64', '66'])).
% 0.19/0.49  thf('68', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('69', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('70', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('71', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('72', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('split', [status(esa)], ['8'])).
% 0.19/0.49  thf('73', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X12)
% 0.19/0.49          | ~ (r1_tsep_1 @ X13 @ X12)
% 0.19/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.19/0.49          | ~ (l1_struct_0 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.49  thf('74', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['72', '73'])).
% 0.19/0.49  thf('75', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['71', '74'])).
% 0.19/0.49  thf('76', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('77', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['75', '76'])).
% 0.19/0.49  thf('78', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_C)
% 0.19/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['70', '77'])).
% 0.19/0.49  thf('79', plain, ((l1_pre_topc @ sk_C)),
% 0.19/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('80', plain,
% 0.19/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['78', '79'])).
% 0.19/0.49  thf('81', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B))
% 0.19/0.49          | ~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['43', '47'])).
% 0.19/0.49  thf('82', plain,
% 0.19/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['80', '81'])).
% 0.19/0.49  thf('83', plain,
% 0.19/0.49      (![X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X12)
% 0.19/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.19/0.49          | (r1_tsep_1 @ X13 @ X12)
% 0.19/0.49          | ~ (l1_struct_0 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.19/0.49  thf('84', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['82', '83'])).
% 0.19/0.49  thf('85', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.19/0.49         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['69', '84'])).
% 0.19/0.49  thf('86', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('87', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['85', '86'])).
% 0.19/0.49  thf('88', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['68', '87'])).
% 0.19/0.49  thf('89', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.49  thf('90', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['88', '89'])).
% 0.19/0.49  thf('91', plain,
% 0.19/0.49      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['65'])).
% 0.19/0.49  thf('92', plain,
% 0.19/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['90', '91'])).
% 0.19/0.49  thf('93', plain,
% 0.19/0.49      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.19/0.49      inference('split', [status(esa)], ['65'])).
% 0.19/0.49  thf('94', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('95', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.49  thf('96', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['88', '89'])).
% 0.19/0.49  thf('97', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X14)
% 0.19/0.49          | ~ (l1_struct_0 @ X15)
% 0.19/0.49          | (r1_tsep_1 @ X15 @ X14)
% 0.19/0.49          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.19/0.49  thf('98', plain,
% 0.19/0.49      ((((r1_tsep_1 @ sk_B @ sk_D)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['96', '97'])).
% 0.19/0.49  thf('99', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.19/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.19/0.49         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['95', '98'])).
% 0.19/0.49  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.49  thf('101', plain,
% 0.19/0.49      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['99', '100'])).
% 0.19/0.49  thf('102', plain,
% 0.19/0.49      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.19/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['94', '101'])).
% 0.19/0.49  thf('103', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('104', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.19/0.49      inference('demod', [status(thm)], ['102', '103'])).
% 0.19/0.49  thf('105', plain,
% 0.19/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.19/0.49      inference('split', [status(esa)], ['65'])).
% 0.19/0.49  thf('106', plain,
% 0.19/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['104', '105'])).
% 0.19/0.49  thf('107', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.19/0.49      inference('split', [status(esa)], ['8'])).
% 0.19/0.49  thf('108', plain, (((r1_tsep_1 @ sk_C @ sk_D))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)],
% 0.19/0.49                ['67', '92', '93', '106', '107'])).
% 0.19/0.49  thf('109', plain,
% 0.19/0.49      (((r1_tsep_1 @ sk_B @ sk_D)
% 0.19/0.49        | ~ (l1_struct_0 @ sk_B)
% 0.19/0.49        | ~ (l1_struct_0 @ sk_D))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['63', '108'])).
% 0.19/0.49  thf('110', plain,
% 0.19/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.19/0.49        | ~ (l1_struct_0 @ sk_D)
% 0.19/0.49        | (r1_tsep_1 @ sk_B @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '109'])).
% 0.19/0.49  thf('111', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('demod', [status(thm)], ['58', '59'])).
% 0.19/0.49  thf('112', plain, ((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D))),
% 0.19/0.49      inference('demod', [status(thm)], ['110', '111'])).
% 0.19/0.49  thf('113', plain,
% 0.19/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.19/0.49      inference('split', [status(esa)], ['65'])).
% 0.19/0.49  thf('114', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['67', '92', '107', '93'])).
% 0.19/0.49  thf('115', plain, (~ (r1_tsep_1 @ sk_B @ sk_D)),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['113', '114'])).
% 0.19/0.49  thf('116', plain, (~ (l1_struct_0 @ sk_D)),
% 0.19/0.49      inference('clc', [status(thm)], ['112', '115'])).
% 0.19/0.49  thf('117', plain, (~ (l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '116'])).
% 0.19/0.49  thf('118', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('119', plain, ($false), inference('demod', [status(thm)], ['117', '118'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
