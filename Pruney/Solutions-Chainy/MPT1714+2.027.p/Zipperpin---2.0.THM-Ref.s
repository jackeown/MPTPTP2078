%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SBSpyeul85

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 789 expanded)
%              Number of leaves         :   22 ( 232 expanded)
%              Depth                    :   32
%              Number of atoms          :  879 (11727 expanded)
%              Number of equality atoms :    3 (  18 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_tsep_1 @ X10 @ X9 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X15 )
      | ( r1_tarski @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
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

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ( r1_tsep_1 @ X10 @ X9 )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('50',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_tsep_1 @ X10 @ X9 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('59',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('62',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('65',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('67',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ( r1_tsep_1 @ X10 @ X9 )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('69',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['54','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('72',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['53','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('81',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['52','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('84',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['51','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('87',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['88'])).

thf('90',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('92',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['88'])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['88'])).

thf('95',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('96',plain,(
    r1_tsep_1 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['90','93','94','95'])).

thf('97',plain,
    ( ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['50','96'])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['3','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('100',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['2','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('103',plain,(
    r1_tsep_1 @ sk_D @ sk_B ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('105',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['1','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('108',plain,
    ( ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['88'])).

thf('110',plain,(
    r1_tsep_1 @ sk_D @ sk_B ),
    inference(demod,[status(thm)],['101','102'])).

thf('111',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['88'])).

thf('112',plain,(
    r1_tsep_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['88'])).

thf('114',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['109','114'])).

thf('116',plain,(
    ~ ( l1_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['108','115'])).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SBSpyeul85
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 80 iterations in 0.033s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(dt_l1_pre_topc, axiom,
% 0.21/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.47  thf('0', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('1', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('2', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('3', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('4', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('5', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('6', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('7', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf(t23_tmap_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.47               ( ![D:$i]:
% 0.21/0.47                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.47                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.47                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.21/0.47                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.47                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47            ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.47                  ( ![D:$i]:
% 0.21/0.47                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.47                      ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.47                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.21/0.47                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.47                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.21/0.47  thf('8', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('split', [status(esa)], ['8'])).
% 0.21/0.47  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.47       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         (~ (l1_struct_0 @ X11)
% 0.21/0.47          | ~ (l1_struct_0 @ X12)
% 0.21/0.47          | (r1_tsep_1 @ X12 @ X11)
% 0.21/0.47          | ~ (r1_tsep_1 @ X11 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      ((((r1_tsep_1 @ sk_D @ sk_C)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.47         | (r1_tsep_1 @ sk_D @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.47  thf('13', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_m1_pre_topc, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.47  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '18'])).
% 0.21/0.47  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.47  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '24'])).
% 0.21/0.47  thf(d3_tsep_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_struct_0 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( l1_struct_0 @ B ) =>
% 0.21/0.47           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.47             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (l1_struct_0 @ X9)
% 0.21/0.47          | ~ (r1_tsep_1 @ X10 @ X9)
% 0.21/0.47          | (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.47          | ~ (l1_struct_0 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.47         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.21/0.47         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.47         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '27'])).
% 0.21/0.47  thf('29', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.47         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.47         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '30'])).
% 0.21/0.47  thf('32', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t4_tsep_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.47               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.21/0.47                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.47          | ~ (m1_pre_topc @ X13 @ X15)
% 0.21/0.47          | (r1_tarski @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))
% 0.21/0.47          | ~ (m1_pre_topc @ X15 @ X14)
% 0.21/0.47          | ~ (l1_pre_topc @ X14)
% 0.21/0.47          | ~ (v2_pre_topc @ X14))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v2_pre_topc @ sk_A)
% 0.21/0.47          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.47  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.47          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.21/0.47      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 0.21/0.47        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['34', '40'])).
% 0.21/0.47  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('43', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.47  thf(t12_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.47         = (u1_struct_0 @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.47  thf(t70_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.21/0.47            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.21/0.47       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.47            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X2 @ X3)
% 0.21/0.47          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X5)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.47  thf('47', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.47          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.47  thf('48', plain,
% 0.21/0.47      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['33', '47'])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (l1_struct_0 @ X9)
% 0.21/0.47          | ~ (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.47          | (r1_tsep_1 @ X10 @ X9)
% 0.21/0.47          | ~ (l1_struct_0 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.47  thf('50', plain,
% 0.21/0.47      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.47         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.47  thf('51', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('52', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('53', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('54', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('55', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('56', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('57', plain,
% 0.21/0.47      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('split', [status(esa)], ['8'])).
% 0.21/0.47  thf('58', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (l1_struct_0 @ X9)
% 0.21/0.47          | ~ (r1_tsep_1 @ X10 @ X9)
% 0.21/0.47          | (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.47          | ~ (l1_struct_0 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.47  thf('59', plain,
% 0.21/0.47      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.47         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.21/0.47         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.47  thf('60', plain,
% 0.21/0.47      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.47         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['56', '59'])).
% 0.21/0.47  thf('61', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('62', plain,
% 0.21/0.47      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.47         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.47  thf('63', plain,
% 0.21/0.47      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.47         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['55', '62'])).
% 0.21/0.47  thf('64', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('65', plain,
% 0.21/0.47      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.47  thf('66', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.47          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.47  thf('67', plain,
% 0.21/0.47      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.47  thf('68', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (l1_struct_0 @ X9)
% 0.21/0.47          | ~ (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.21/0.47          | (r1_tsep_1 @ X10 @ X9)
% 0.21/0.47          | ~ (l1_struct_0 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.47  thf('69', plain,
% 0.21/0.47      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.47         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.47  thf('70', plain,
% 0.21/0.47      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.47         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['54', '69'])).
% 0.21/0.47  thf('71', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('72', plain,
% 0.21/0.47      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.47  thf('73', plain,
% 0.21/0.47      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['53', '72'])).
% 0.21/0.47  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('75', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.47  thf('76', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.47  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.47  thf('79', plain,
% 0.21/0.47      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['73', '78'])).
% 0.21/0.47  thf('80', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         (~ (l1_struct_0 @ X11)
% 0.21/0.47          | ~ (l1_struct_0 @ X12)
% 0.21/0.47          | (r1_tsep_1 @ X12 @ X11)
% 0.21/0.47          | ~ (r1_tsep_1 @ X11 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.47  thf('81', plain,
% 0.21/0.47      ((((r1_tsep_1 @ sk_B @ sk_D)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.47  thf('82', plain,
% 0.21/0.47      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.47         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.47         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['52', '81'])).
% 0.21/0.47  thf('83', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.47  thf('84', plain,
% 0.21/0.47      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.47  thf('85', plain,
% 0.21/0.47      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.47         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['51', '84'])).
% 0.21/0.47  thf('86', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('87', plain,
% 0.21/0.47      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['85', '86'])).
% 0.21/0.47  thf('88', plain,
% 0.21/0.47      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('89', plain,
% 0.21/0.47      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.47      inference('split', [status(esa)], ['88'])).
% 0.21/0.47  thf('90', plain,
% 0.21/0.47      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['87', '89'])).
% 0.21/0.47  thf('91', plain,
% 0.21/0.47      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.47      inference('demod', [status(thm)], ['73', '78'])).
% 0.21/0.47  thf('92', plain,
% 0.21/0.47      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['88'])).
% 0.21/0.47  thf('93', plain,
% 0.21/0.47      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.47  thf('94', plain,
% 0.21/0.47      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.47      inference('split', [status(esa)], ['88'])).
% 0.21/0.47  thf('95', plain, (((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.47      inference('split', [status(esa)], ['8'])).
% 0.21/0.47  thf('96', plain, (((r1_tsep_1 @ sk_C @ sk_D))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['90', '93', '94', '95'])).
% 0.21/0.47  thf('97', plain,
% 0.21/0.47      ((~ (l1_struct_0 @ sk_D)
% 0.21/0.47        | (r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.47        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['50', '96'])).
% 0.21/0.47  thf('98', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_D)
% 0.21/0.47        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.47        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '97'])).
% 0.21/0.47  thf('99', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('100', plain, ((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['98', '99'])).
% 0.21/0.47  thf('101', plain, ((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '100'])).
% 0.21/0.47  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.47  thf('103', plain, ((r1_tsep_1 @ sk_D @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['101', '102'])).
% 0.21/0.47  thf('104', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         (~ (l1_struct_0 @ X11)
% 0.21/0.47          | ~ (l1_struct_0 @ X12)
% 0.21/0.47          | (r1_tsep_1 @ X12 @ X11)
% 0.21/0.47          | ~ (r1_tsep_1 @ X11 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.47  thf('105', plain,
% 0.21/0.47      (((r1_tsep_1 @ sk_B @ sk_D)
% 0.21/0.47        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.47        | ~ (l1_struct_0 @ sk_D))),
% 0.21/0.47      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.47  thf('106', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.47        | ~ (l1_struct_0 @ sk_D)
% 0.21/0.47        | (r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '105'])).
% 0.21/0.47  thf('107', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.47  thf('108', plain, ((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.47      inference('demod', [status(thm)], ['106', '107'])).
% 0.21/0.47  thf('109', plain,
% 0.21/0.47      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.47      inference('split', [status(esa)], ['88'])).
% 0.21/0.47  thf('110', plain, ((r1_tsep_1 @ sk_D @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['101', '102'])).
% 0.21/0.47  thf('111', plain,
% 0.21/0.47      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.21/0.47      inference('split', [status(esa)], ['88'])).
% 0.21/0.47  thf('112', plain, (((r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['110', '111'])).
% 0.21/0.47  thf('113', plain,
% 0.21/0.47      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.47      inference('split', [status(esa)], ['88'])).
% 0.21/0.47  thf('114', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['112', '113'])).
% 0.21/0.47  thf('115', plain, (~ (r1_tsep_1 @ sk_B @ sk_D)),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['109', '114'])).
% 0.21/0.47  thf('116', plain, (~ (l1_struct_0 @ sk_D)),
% 0.21/0.47      inference('clc', [status(thm)], ['108', '115'])).
% 0.21/0.47  thf('117', plain, (~ (l1_pre_topc @ sk_D)),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '116'])).
% 0.21/0.47  thf('118', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('119', plain, ($false), inference('demod', [status(thm)], ['117', '118'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
