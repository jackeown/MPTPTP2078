%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vzCLhueAk4

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 794 expanded)
%              Number of leaves         :   21 ( 231 expanded)
%              Depth                    :   32
%              Number of atoms          :  876 (11709 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( r1_tsep_1 @ X12 @ X13 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_struct_0 @ X10 )
      | ~ ( r1_tsep_1 @ X11 @ X10 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X16 )
      | ( r1_tarski @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_pre_topc @ X16 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_struct_0 @ X10 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X10 ) )
      | ( r1_tsep_1 @ X11 @ X10 )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('51',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_struct_0 @ X10 )
      | ~ ( r1_tsep_1 @ X11 @ X10 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('60',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('63',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('66',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('68',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_struct_0 @ X10 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X10 ) )
      | ( r1_tsep_1 @ X11 @ X10 )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('70',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['55','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('73',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['54','73'])).

thf('75',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( r1_tsep_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('82',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['53','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('85',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['52','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('88',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['89'])).

thf('94',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['89'])).

thf('96',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('97',plain,(
    r1_tsep_1 @ sk_C @ sk_D ),
    inference('sat_resolution*',[status(thm)],['91','94','95','96'])).

thf('98',plain,
    ( ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['51','97'])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['3','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('101',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['2','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('104',plain,(
    r1_tsep_1 @ sk_D @ sk_B ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( l1_struct_0 @ X13 )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( r1_tsep_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('106',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['1','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('109',plain,
    ( ~ ( l1_struct_0 @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['89'])).

thf('111',plain,(
    r1_tsep_1 @ sk_D @ sk_B ),
    inference(demod,[status(thm)],['102','103'])).

thf('112',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['89'])).

thf('113',plain,(
    r1_tsep_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['89'])).

thf('115',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['110','115'])).

thf('117',plain,(
    ~ ( l1_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['109','116'])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vzCLhueAk4
% 0.13/0.36  % Computer   : n019.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 16:45:38 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 80 iterations in 0.034s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.51  thf(dt_l1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.51  thf('0', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('1', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('2', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('3', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('4', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('5', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('6', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('7', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf(t23_tmap_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.51                   ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.51                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.22/0.51                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.22/0.51                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.51            ( l1_pre_topc @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.51              ( ![C:$i]:
% 0.22/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.51                  ( ![D:$i]:
% 0.22/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.51                      ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.51                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.22/0.51                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.22/0.51                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.22/0.51  thf('8', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('split', [status(esa)], ['8'])).
% 0.22/0.51  thf(symmetry_r1_tsep_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.22/0.51       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X12)
% 0.22/0.51          | ~ (l1_struct_0 @ X13)
% 0.22/0.51          | (r1_tsep_1 @ X13 @ X12)
% 0.22/0.51          | ~ (r1_tsep_1 @ X12 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      ((((r1_tsep_1 @ sk_D @ sk_C)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C)
% 0.22/0.51         | (r1_tsep_1 @ sk_D @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '11'])).
% 0.22/0.51  thf('13', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_m1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.51  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('17', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['12', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '18'])).
% 0.22/0.51  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.51  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.22/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('24', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['19', '24'])).
% 0.22/0.51  thf(d3_tsep_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_struct_0 @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( l1_struct_0 @ B ) =>
% 0.22/0.51           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.22/0.51             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X10)
% 0.22/0.51          | ~ (r1_tsep_1 @ X11 @ X10)
% 0.22/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X10))
% 0.22/0.51          | ~ (l1_struct_0 @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '27'])).
% 0.22/0.51  thf('29', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_C)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_C)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '30'])).
% 0.22/0.51  thf('32', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.51  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t4_tsep_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.51               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.22/0.51                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X14 @ X15)
% 0.22/0.51          | ~ (m1_pre_topc @ X14 @ X16)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X16))
% 0.22/0.51          | ~ (m1_pre_topc @ X16 @ X15)
% 0.22/0.51          | ~ (l1_pre_topc @ X15)
% 0.22/0.51          | ~ (v2_pre_topc @ X15))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v2_pre_topc @ sk_A)
% 0.22/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.51  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.22/0.51          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.22/0.51          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 0.22/0.51        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['34', '40'])).
% 0.22/0.51  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('43', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.22/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.51  thf(d10_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.51  thf('45', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.51      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.51  thf(t64_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.22/0.51         ( r1_xboole_0 @ B @ D ) ) =>
% 0.22/0.51       ( r1_xboole_0 @ A @ C ) ))).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X3 @ X4)
% 0.22/0.51          | ~ (r1_tarski @ X3 @ X5)
% 0.22/0.51          | ~ (r1_tarski @ X4 @ X6)
% 0.22/0.51          | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.51          | ~ (r1_tarski @ X2 @ X1)
% 0.22/0.51          | (r1_xboole_0 @ X0 @ X2))),
% 0.22/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51          | ~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['43', '47'])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['33', '48'])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X10)
% 0.22/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X10))
% 0.22/0.51          | (r1_tsep_1 @ X11 @ X10)
% 0.22/0.51          | ~ (l1_struct_0 @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.22/0.51         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.51  thf('52', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('53', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('54', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('55', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('56', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('57', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('58', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('split', [status(esa)], ['8'])).
% 0.22/0.51  thf('59', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X10)
% 0.22/0.51          | ~ (r1_tsep_1 @ X11 @ X10)
% 0.22/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X10))
% 0.22/0.51          | ~ (l1_struct_0 @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.51  thf('60', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.51  thf('61', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['57', '60'])).
% 0.22/0.51  thf('62', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('63', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_C)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_C)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['56', '63'])).
% 0.22/0.51  thf('65', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('66', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.51  thf('67', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B))
% 0.22/0.51          | ~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['43', '47'])).
% 0.22/0.51  thf('68', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.51  thf('69', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X10)
% 0.22/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X10))
% 0.22/0.51          | (r1_tsep_1 @ X11 @ X10)
% 0.22/0.51          | ~ (l1_struct_0 @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.51  thf('70', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.22/0.51         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.51  thf('71', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.22/0.51         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['55', '70'])).
% 0.22/0.51  thf('72', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('73', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['71', '72'])).
% 0.22/0.51  thf('74', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['54', '73'])).
% 0.22/0.51  thf('75', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('76', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.51  thf('77', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.51  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('79', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.51  thf('80', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['74', '79'])).
% 0.22/0.51  thf('81', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X12)
% 0.22/0.51          | ~ (l1_struct_0 @ X13)
% 0.22/0.51          | (r1_tsep_1 @ X13 @ X12)
% 0.22/0.51          | ~ (r1_tsep_1 @ X12 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.51  thf('82', plain,
% 0.22/0.51      ((((r1_tsep_1 @ sk_B @ sk_D)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['80', '81'])).
% 0.22/0.51  thf('83', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_B)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.22/0.51         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['53', '82'])).
% 0.22/0.51  thf('84', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.51  thf('85', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['83', '84'])).
% 0.22/0.51  thf('86', plain,
% 0.22/0.51      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['52', '85'])).
% 0.22/0.51  thf('87', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('88', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['86', '87'])).
% 0.22/0.51  thf('89', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('90', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.22/0.51      inference('split', [status(esa)], ['89'])).
% 0.22/0.51  thf('91', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.22/0.51      inference('sup-', [status(thm)], ['88', '90'])).
% 0.22/0.51  thf('92', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.22/0.51      inference('demod', [status(thm)], ['74', '79'])).
% 0.22/0.51  thf('93', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.22/0.51      inference('split', [status(esa)], ['89'])).
% 0.22/0.51  thf('94', plain,
% 0.22/0.51      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['92', '93'])).
% 0.22/0.51  thf('95', plain,
% 0.22/0.51      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.22/0.51      inference('split', [status(esa)], ['89'])).
% 0.22/0.51  thf('96', plain, (((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.22/0.51      inference('split', [status(esa)], ['8'])).
% 0.22/0.51  thf('97', plain, (((r1_tsep_1 @ sk_C @ sk_D))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['91', '94', '95', '96'])).
% 0.22/0.51  thf('98', plain,
% 0.22/0.51      ((~ (l1_struct_0 @ sk_D)
% 0.22/0.51        | (r1_tsep_1 @ sk_D @ sk_B)
% 0.22/0.51        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['51', '97'])).
% 0.22/0.51  thf('99', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_D)
% 0.22/0.51        | ~ (l1_struct_0 @ sk_B)
% 0.22/0.51        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '98'])).
% 0.22/0.51  thf('100', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('101', plain, ((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['99', '100'])).
% 0.22/0.51  thf('102', plain, ((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['2', '101'])).
% 0.22/0.51  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.51  thf('104', plain, ((r1_tsep_1 @ sk_D @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['102', '103'])).
% 0.22/0.51  thf('105', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X12)
% 0.22/0.51          | ~ (l1_struct_0 @ X13)
% 0.22/0.51          | (r1_tsep_1 @ X13 @ X12)
% 0.22/0.51          | ~ (r1_tsep_1 @ X12 @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.51  thf('106', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_B @ sk_D)
% 0.22/0.51        | ~ (l1_struct_0 @ sk_B)
% 0.22/0.51        | ~ (l1_struct_0 @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['104', '105'])).
% 0.22/0.51  thf('107', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.51        | ~ (l1_struct_0 @ sk_D)
% 0.22/0.51        | (r1_tsep_1 @ sk_B @ sk_D))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '106'])).
% 0.22/0.51  thf('108', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.51  thf('109', plain, ((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D))),
% 0.22/0.51      inference('demod', [status(thm)], ['107', '108'])).
% 0.22/0.51  thf('110', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.22/0.51      inference('split', [status(esa)], ['89'])).
% 0.22/0.51  thf('111', plain, ((r1_tsep_1 @ sk_D @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['102', '103'])).
% 0.22/0.51  thf('112', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.22/0.51      inference('split', [status(esa)], ['89'])).
% 0.22/0.51  thf('113', plain, (((r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['111', '112'])).
% 0.22/0.51  thf('114', plain,
% 0.22/0.51      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.22/0.51      inference('split', [status(esa)], ['89'])).
% 0.22/0.51  thf('115', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['113', '114'])).
% 0.22/0.51  thf('116', plain, (~ (r1_tsep_1 @ sk_B @ sk_D)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['110', '115'])).
% 0.22/0.51  thf('117', plain, (~ (l1_struct_0 @ sk_D)),
% 0.22/0.51      inference('clc', [status(thm)], ['109', '116'])).
% 0.22/0.51  thf('118', plain, (~ (l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '117'])).
% 0.22/0.51  thf('119', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('120', plain, ($false), inference('demod', [status(thm)], ['118', '119'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
