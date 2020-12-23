%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.elk7i0p8H7

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 247 expanded)
%              Number of leaves         :   23 (  80 expanded)
%              Depth                    :   23
%              Number of atoms          :  655 (2711 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X13 )
      | ( r1_tarski @ ( u1_struct_0 @ X11 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_pre_topc @ X13 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('14',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X10 )
      | ( r1_tsep_1 @ X10 @ X9 )
      | ~ ( r1_tsep_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('20',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['15','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['28','33'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ~ ( r1_tsep_1 @ X8 @ X7 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('36',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['14','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('39',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('44',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['12','44'])).

thf('46',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['2','45'])).

thf('47',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['1','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    ! [X2: $i] :
      ( ( ( k2_struct_0 @ X2 )
        = ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('54',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['17'])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_struct_0 @ X7 )
      | ~ ( r1_tsep_1 @ X8 @ X7 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('58',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('61',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('64',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('66',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['53','66'])).

thf('68',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['52','67'])).

thf('69',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['51','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('72',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['50','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('78',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['17'])).

thf('80',plain,(
    r1_tsep_1 @ sk_C @ sk_B ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['49','80'])).

thf('82',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['86','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.elk7i0p8H7
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:21:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 119 iterations in 0.046s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(dt_l1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.50  thf('0', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('1', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf(d3_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X2 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf(t22_tmap_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50               ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.50                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50                  ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.50                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.20/0.50  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain, ((m1_pre_topc @ sk_B @ sk_A)),
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
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.50          | ~ (m1_pre_topc @ X11 @ X13)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X13))
% 0.20/0.50          | ~ (m1_pre_topc @ X13 @ X12)
% 0.20/0.50          | ~ (l1_pre_topc @ X12)
% 0.20/0.50          | ~ (v2_pre_topc @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.50          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 0.20/0.50        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '9'])).
% 0.20/0.50  thf('11', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('14', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('15', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('16', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('17', plain, (((r1_tsep_1 @ sk_B @ sk_C) | (r1_tsep_1 @ sk_C @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_C @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['17'])).
% 0.20/0.50  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.50       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X9)
% 0.20/0.50          | ~ (l1_struct_0 @ X10)
% 0.20/0.50          | (r1_tsep_1 @ X10 @ X9)
% 0.20/0.50          | ~ (r1_tsep_1 @ X9 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((((r1_tsep_1 @ sk_B @ sk_C)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.50         | (r1_tsep_1 @ sk_B @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '20'])).
% 0.20/0.50  thf('22', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_m1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('24', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_B @ sk_C)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_B @ sk_C)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '27'])).
% 0.20/0.50  thf('29', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('31', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '33'])).
% 0.20/0.50  thf(d3_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_struct_0 @ B ) =>
% 0.20/0.50           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.50             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X7)
% 0.20/0.50          | ~ (r1_tsep_1 @ X8 @ X7)
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l1_struct_0 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '36'])).
% 0.20/0.50  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_C)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_C)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '39'])).
% 0.20/0.50  thf('41', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf(t69_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.50       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ X0 @ X1)
% 0.20/0.50          | (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50         | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((((v1_xboole_0 @ (k2_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['2', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '46'])).
% 0.20/0.50  thf('48', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('51', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X2 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X2) = (u1_struct_0 @ X2)) | ~ (l1_struct_0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf('53', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('54', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('55', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_C)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('split', [status(esa)], ['17'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X7)
% 0.20/0.50          | ~ (r1_tsep_1 @ X8 @ X7)
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X7))
% 0.20/0.50          | ~ (l1_struct_0 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['55', '58'])).
% 0.20/0.50  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_C)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_C)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['54', '61'])).
% 0.20/0.50  thf('63', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.50          | ~ (r1_tarski @ X0 @ X1)
% 0.20/0.50          | (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50         | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '66'])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      ((((v1_xboole_0 @ (k2_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['52', '67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (((~ (l1_pre_topc @ sk_B) | (v1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['51', '68'])).
% 0.20/0.50  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf(fc5_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (![X6 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ (k2_struct_0 @ X6))
% 0.20/0.50          | ~ (l1_struct_0 @ X6)
% 0.20/0.50          | (v2_struct_0 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.50  thf('74', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('75', plain, ((~ (l1_struct_0 @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.50  thf('76', plain, ((~ (l1_pre_topc @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '75'])).
% 0.20/0.50  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('78', plain, (~ ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.50  thf('79', plain, (((r1_tsep_1 @ sk_C @ sk_B)) | ((r1_tsep_1 @ sk_B @ sk_C))),
% 0.20/0.50      inference('split', [status(esa)], ['17'])).
% 0.20/0.50  thf('80', plain, (((r1_tsep_1 @ sk_C @ sk_B))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.20/0.50  thf('81', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_B))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['49', '80'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (![X6 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ (k2_struct_0 @ X6))
% 0.20/0.50          | ~ (l1_struct_0 @ X6)
% 0.20/0.50          | (v2_struct_0 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.20/0.50  thf('83', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.50  thf('84', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('85', plain, (~ (l1_struct_0 @ sk_B)),
% 0.20/0.50      inference('clc', [status(thm)], ['83', '84'])).
% 0.20/0.50  thf('86', plain, (~ (l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '85'])).
% 0.20/0.50  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('88', plain, ($false), inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
