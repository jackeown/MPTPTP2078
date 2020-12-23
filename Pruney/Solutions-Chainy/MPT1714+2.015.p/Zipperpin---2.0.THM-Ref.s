%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aBvnSG7sIM

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:20 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 789 expanded)
%              Number of leaves         :   22 ( 232 expanded)
%              Depth                    :   35
%              Number of atoms          :  882 (11666 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( r1_tsep_1 @ X24 @ X23 )
      | ~ ( r1_tsep_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('11',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_tsep_1 @ sk_D @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_tsep_1 @ sk_D @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_tsep_1 @ sk_D @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X21 )
      | ~ ( r1_tsep_1 @ X22 @ X21 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('27',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('30',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('33',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
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

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ~ ( m1_pre_topc @ X25 @ X27 )
      | ( r1_tarski @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['35','47'])).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X21 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ( r1_tsep_1 @ X22 @ X21 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('50',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('60',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( r1_tsep_1 @ X24 @ X23 )
      | ~ ( r1_tsep_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('62',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('70',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X21 )
      | ~ ( r1_tsep_1 @ X22 @ X21 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('71',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('74',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('77',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('79',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('81',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X21 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ( r1_tsep_1 @ X22 @ X21 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('83',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['66','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('86',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['65','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('89',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( r1_tsep_1 @ X24 @ X23 )
      | ~ ( r1_tsep_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('91',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r1_tsep_1 @ sk_B_1 @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B_1 )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B_1 ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('95',plain,
    ( ~ ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['92'])).

thf('96',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('98',plain,
    ( ~ ( r1_tsep_1 @ sk_B_1 @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['92'])).

thf('99',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('101',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B_1 )
    | ~ ( r1_tsep_1 @ sk_B_1 @ sk_D ) ),
    inference(split,[status(esa)],['92'])).

thf('102',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['96','99','100','101'])).

thf('103',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['93','102'])).

thf('104',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(clc,[status(thm)],['91','103'])).

thf('105',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('107',plain,
    ( ~ ( l1_struct_0 @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('110',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['110','100'])).

thf('112',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['62','111'])).

thf('113',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['93','102'])).

thf('114',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('117',plain,(
    ~ ( l1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['0','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['118','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aBvnSG7sIM
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 215 iterations in 0.108s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.37/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.37/0.56  thf(dt_l1_pre_topc, axiom,
% 0.37/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.56  thf('0', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('1', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('2', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('3', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('4', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('5', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('6', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('7', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf(t23_tmap_1, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.37/0.56               ( ![D:$i]:
% 0.37/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.37/0.56                   ( ( m1_pre_topc @ B @ C ) =>
% 0.37/0.56                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.37/0.56                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.37/0.56                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.37/0.56            ( l1_pre_topc @ A ) ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.37/0.56              ( ![C:$i]:
% 0.37/0.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.37/0.56                  ( ![D:$i]:
% 0.37/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.37/0.56                      ( ( m1_pre_topc @ B @ C ) =>
% 0.37/0.56                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.37/0.56                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.37/0.56                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_C_1 @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_C_1 @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('split', [status(esa)], ['8'])).
% 0.37/0.56  thf(symmetry_r1_tsep_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.37/0.56       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X23 : $i, X24 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X23)
% 0.37/0.56          | ~ (l1_struct_0 @ X24)
% 0.37/0.56          | (r1_tsep_1 @ X24 @ X23)
% 0.37/0.56          | ~ (r1_tsep_1 @ X23 @ X24))),
% 0.37/0.56      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      ((((r1_tsep_1 @ sk_D @ sk_C_1)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_D)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_D)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_C_1)
% 0.37/0.56         | (r1_tsep_1 @ sk_D @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['7', '11'])).
% 0.37/0.56  thf('13', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(dt_m1_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X19 @ X20)
% 0.37/0.56          | (l1_pre_topc @ X19)
% 0.37/0.56          | ~ (l1_pre_topc @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.56  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.56  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_C_1) | (r1_tsep_1 @ sk_D @ sk_C_1)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('demod', [status(thm)], ['12', '17'])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_C_1) | (r1_tsep_1 @ sk_D @ sk_C_1)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '18'])).
% 0.37/0.56  thf('20', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X19 @ X20)
% 0.37/0.56          | (l1_pre_topc @ X19)
% 0.37/0.56          | ~ (l1_pre_topc @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.56  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('24', plain, ((l1_pre_topc @ sk_C_1)),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_D @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.56  thf(d3_tsep_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_struct_0 @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( l1_struct_0 @ B ) =>
% 0.37/0.56           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.37/0.56             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X21 : $i, X22 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X21)
% 0.37/0.56          | ~ (r1_tsep_1 @ X22 @ X21)
% 0.37/0.56          | (r1_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.37/0.56          | ~ (l1_struct_0 @ X22))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_D)
% 0.37/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_D)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_C_1)
% 0.37/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '27'])).
% 0.37/0.56  thf('29', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_C_1)
% 0.37/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_C_1)
% 0.37/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['4', '30'])).
% 0.37/0.56  thf('32', plain, ((l1_pre_topc @ sk_C_1)),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.37/0.56  thf(t83_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      ((((k4_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.37/0.56          = (u1_struct_0 @ sk_D)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.56  thf('36', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('37', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t4_tsep_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_pre_topc @ C @ A ) =>
% 0.37/0.56               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.37/0.56                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X25 @ X26)
% 0.37/0.56          | ~ (m1_pre_topc @ X25 @ X27)
% 0.37/0.56          | (r1_tarski @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X27))
% 0.37/0.56          | ~ (m1_pre_topc @ X27 @ X26)
% 0.37/0.56          | ~ (l1_pre_topc @ X26)
% 0.37/0.56          | ~ (v2_pre_topc @ X26))),
% 0.37/0.56      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (v2_pre_topc @ sk_A)
% 0.37/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.37/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ X0))
% 0.37/0.56          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.56  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.37/0.56          | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ X0))
% 0.37/0.56          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      ((~ (m1_pre_topc @ sk_B_1 @ sk_C_1)
% 0.37/0.56        | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['36', '42'])).
% 0.37/0.56  thf('44', plain, ((m1_pre_topc @ sk_B_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))),
% 0.37/0.56      inference('demod', [status(thm)], ['43', '44'])).
% 0.37/0.56  thf(t85_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X13 @ X14)
% 0.37/0.56          | (r1_xboole_0 @ X13 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ 
% 0.37/0.56          (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_D)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['35', '47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (![X21 : $i, X22 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X21)
% 0.37/0.56          | ~ (r1_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.37/0.56          | (r1_tsep_1 @ X22 @ X21)
% 0.37/0.56          | ~ (l1_struct_0 @ X22))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_B_1)
% 0.37/0.56         | (r1_tsep_1 @ sk_B_1 @ sk_D)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_B_1)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_D)
% 0.37/0.56         | (r1_tsep_1 @ sk_B_1 @ sk_D))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['3', '50'])).
% 0.37/0.56  thf('52', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i]:
% 0.37/0.56         (~ (m1_pre_topc @ X19 @ X20)
% 0.37/0.56          | (l1_pre_topc @ X19)
% 0.37/0.56          | ~ (l1_pre_topc @ X20))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.37/0.56  thf('54', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.56  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('56', plain, ((l1_pre_topc @ sk_B_1)),
% 0.37/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B_1 @ sk_D)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('demod', [status(thm)], ['51', '56'])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B_1 @ sk_D)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '57'])).
% 0.37/0.56  thf('59', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_B_1 @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('demod', [status(thm)], ['58', '59'])).
% 0.37/0.56  thf('61', plain,
% 0.37/0.56      (![X23 : $i, X24 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X23)
% 0.37/0.56          | ~ (l1_struct_0 @ X24)
% 0.37/0.56          | (r1_tsep_1 @ X24 @ X23)
% 0.37/0.56          | ~ (r1_tsep_1 @ X23 @ X24))),
% 0.37/0.56      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.37/0.56  thf('62', plain,
% 0.37/0.56      ((((r1_tsep_1 @ sk_D @ sk_B_1)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_D)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.37/0.56  thf('63', plain,
% 0.37/0.56      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('64', plain,
% 0.37/0.56      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('67', plain,
% 0.37/0.56      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_D @ sk_C_1)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('split', [status(esa)], ['8'])).
% 0.37/0.56  thf('70', plain,
% 0.37/0.56      (![X21 : $i, X22 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X21)
% 0.37/0.56          | ~ (r1_tsep_1 @ X22 @ X21)
% 0.37/0.56          | (r1_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.37/0.56          | ~ (l1_struct_0 @ X22))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_D)
% 0.37/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.37/0.56         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_D)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_C_1)
% 0.37/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['68', '71'])).
% 0.37/0.56  thf('73', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('74', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_C_1)
% 0.37/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['72', '73'])).
% 0.37/0.56  thf('75', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_C_1)
% 0.37/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['67', '74'])).
% 0.37/0.56  thf('76', plain, ((l1_pre_topc @ sk_C_1)),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf('77', plain,
% 0.37/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.56  thf('78', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.56  thf('79', plain,
% 0.37/0.56      ((((k4_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C_1))
% 0.37/0.56          = (u1_struct_0 @ sk_D)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['77', '78'])).
% 0.37/0.56  thf('80', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ 
% 0.37/0.56          (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('81', plain,
% 0.37/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_D)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup+', [status(thm)], ['79', '80'])).
% 0.37/0.56  thf('82', plain,
% 0.37/0.56      (![X21 : $i, X22 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X21)
% 0.37/0.56          | ~ (r1_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.37/0.56          | (r1_tsep_1 @ X22 @ X21)
% 0.37/0.56          | ~ (l1_struct_0 @ X22))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.37/0.56  thf('83', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_B_1)
% 0.37/0.56         | (r1_tsep_1 @ sk_B_1 @ sk_D)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['81', '82'])).
% 0.37/0.56  thf('84', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_B_1)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_D)
% 0.37/0.56         | (r1_tsep_1 @ sk_B_1 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['66', '83'])).
% 0.37/0.56  thf('85', plain, ((l1_pre_topc @ sk_B_1)),
% 0.37/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf('86', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B_1 @ sk_D)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['84', '85'])).
% 0.37/0.56  thf('87', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B_1 @ sk_D)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['65', '86'])).
% 0.37/0.56  thf('88', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('89', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_B_1 @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.56  thf('90', plain,
% 0.37/0.56      (![X23 : $i, X24 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X23)
% 0.37/0.56          | ~ (l1_struct_0 @ X24)
% 0.37/0.56          | (r1_tsep_1 @ X24 @ X23)
% 0.37/0.56          | ~ (r1_tsep_1 @ X23 @ X24))),
% 0.37/0.56      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.37/0.56  thf('91', plain,
% 0.37/0.56      ((((r1_tsep_1 @ sk_D @ sk_B_1)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_D)
% 0.37/0.56         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['89', '90'])).
% 0.37/0.56  thf('92', plain,
% 0.37/0.56      ((~ (r1_tsep_1 @ sk_B_1 @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B_1))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('93', plain,
% 0.37/0.56      ((~ (r1_tsep_1 @ sk_D @ sk_B_1)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B_1)))),
% 0.37/0.56      inference('split', [status(esa)], ['92'])).
% 0.37/0.56  thf('94', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_B_1 @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.37/0.56      inference('demod', [status(thm)], ['58', '59'])).
% 0.37/0.56  thf('95', plain,
% 0.37/0.56      ((~ (r1_tsep_1 @ sk_B_1 @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B_1 @ sk_D)))),
% 0.37/0.56      inference('split', [status(esa)], ['92'])).
% 0.37/0.56  thf('96', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_B_1 @ sk_D)) | ~ ((r1_tsep_1 @ sk_C_1 @ sk_D))),
% 0.37/0.56      inference('sup-', [status(thm)], ['94', '95'])).
% 0.37/0.56  thf('97', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_B_1 @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['87', '88'])).
% 0.37/0.56  thf('98', plain,
% 0.37/0.56      ((~ (r1_tsep_1 @ sk_B_1 @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B_1 @ sk_D)))),
% 0.37/0.56      inference('split', [status(esa)], ['92'])).
% 0.37/0.56  thf('99', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_B_1 @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['97', '98'])).
% 0.37/0.56  thf('100', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_C_1 @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.37/0.56      inference('split', [status(esa)], ['8'])).
% 0.37/0.56  thf('101', plain,
% 0.37/0.56      (~ ((r1_tsep_1 @ sk_D @ sk_B_1)) | ~ ((r1_tsep_1 @ sk_B_1 @ sk_D))),
% 0.37/0.56      inference('split', [status(esa)], ['92'])).
% 0.37/0.56  thf('102', plain, (~ ((r1_tsep_1 @ sk_D @ sk_B_1))),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['96', '99', '100', '101'])).
% 0.37/0.56  thf('103', plain, (~ (r1_tsep_1 @ sk_D @ sk_B_1)),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['93', '102'])).
% 0.37/0.56  thf('104', plain,
% 0.37/0.56      (((~ (l1_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_D)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('clc', [status(thm)], ['91', '103'])).
% 0.37/0.56  thf('105', plain,
% 0.37/0.56      (((~ (l1_pre_topc @ sk_B_1) | ~ (l1_struct_0 @ sk_D)))
% 0.37/0.56         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['64', '104'])).
% 0.37/0.56  thf('106', plain, ((l1_pre_topc @ sk_B_1)),
% 0.37/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf('107', plain,
% 0.37/0.56      ((~ (l1_struct_0 @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['105', '106'])).
% 0.37/0.56  thf('108', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['63', '107'])).
% 0.37/0.56  thf('109', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('110', plain, (~ ((r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.37/0.56      inference('demod', [status(thm)], ['108', '109'])).
% 0.37/0.56  thf('111', plain, (((r1_tsep_1 @ sk_C_1 @ sk_D))),
% 0.37/0.56      inference('sat_resolution*', [status(thm)], ['110', '100'])).
% 0.37/0.56  thf('112', plain,
% 0.37/0.56      (((r1_tsep_1 @ sk_D @ sk_B_1)
% 0.37/0.56        | ~ (l1_struct_0 @ sk_D)
% 0.37/0.56        | ~ (l1_struct_0 @ sk_B_1))),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['62', '111'])).
% 0.37/0.56  thf('113', plain, (~ (r1_tsep_1 @ sk_D @ sk_B_1)),
% 0.37/0.56      inference('simpl_trail', [status(thm)], ['93', '102'])).
% 0.37/0.56  thf('114', plain, ((~ (l1_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_D))),
% 0.37/0.56      inference('clc', [status(thm)], ['112', '113'])).
% 0.37/0.56  thf('115', plain, ((~ (l1_pre_topc @ sk_B_1) | ~ (l1_struct_0 @ sk_D))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '114'])).
% 0.37/0.56  thf('116', plain, ((l1_pre_topc @ sk_B_1)),
% 0.37/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.37/0.56  thf('117', plain, (~ (l1_struct_0 @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['115', '116'])).
% 0.37/0.56  thf('118', plain, (~ (l1_pre_topc @ sk_D)),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '117'])).
% 0.37/0.56  thf('119', plain, ((l1_pre_topc @ sk_D)),
% 0.37/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.37/0.56  thf('120', plain, ($false), inference('demod', [status(thm)], ['118', '119'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
