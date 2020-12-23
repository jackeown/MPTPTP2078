%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZR6SMrMNHD

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 543 expanded)
%              Number of leaves         :   22 ( 164 expanded)
%              Depth                    :   26
%              Number of atoms          :  900 (8001 expanded)
%              Number of equality atoms :    3 (  12 expanded)
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

thf('4',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_tsep_1 @ X10 @ X9 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('7',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X15 )
      | ( r1_tarski @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['21','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ( r1_tsep_1 @ X10 @ X9 )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('38',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['1','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('41',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['48','50'])).

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

thf('57',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['4'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('62',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('65',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('68',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_tsep_1 @ X10 @ X9 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('70',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['57','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('73',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['56','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('76',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('78',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) )
      | ( r1_tsep_1 @ X10 @ X9 )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('80',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['55','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('83',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['54','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('86',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('88',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['53','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('91',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['52','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('94',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['49'])).

thf('96',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('98',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('99',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('100',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('101',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('104',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('107',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['49'])).

thf('109',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['49'])).

thf('111',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('112',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['49'])).

thf('113',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('115',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['51','96','109','110','113','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZR6SMrMNHD
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:09:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 78 iterations in 0.029s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.49  thf(dt_l1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('0', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('1', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('2', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('3', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf(t24_tmap_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.49                   ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.49                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.49                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.20/0.49                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.49            ( l1_pre_topc @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.49                  ( ![D:$i]:
% 0.20/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.49                      ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.49                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.49                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.20/0.49                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.20/0.49  thf('4', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['4'])).
% 0.20/0.49  thf(d3_tsep_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_struct_0 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( l1_struct_0 @ B ) =>
% 0.20/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X9)
% 0.20/0.49          | ~ (r1_tsep_1 @ X10 @ X9)
% 0.20/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.20/0.49          | ~ (l1_struct_0 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.49  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_m1_pre_topc, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_pre_topc @ A ) =>
% 0.20/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '14'])).
% 0.20/0.49  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '20'])).
% 0.20/0.49  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t4_tsep_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.49               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.20/0.49                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.49          | ~ (m1_pre_topc @ X13 @ X15)
% 0.20/0.49          | (r1_tarski @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))
% 0.20/0.49          | ~ (m1_pre_topc @ X15 @ X14)
% 0.20/0.49          | ~ (l1_pre_topc @ X14)
% 0.20/0.49          | ~ (v2_pre_topc @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v2_pre_topc @ sk_A)
% 0.20/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.49          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.49          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.49          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.49          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.49          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 0.20/0.49        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '28'])).
% 0.20/0.49  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf(t12_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.20/0.49         = (u1_struct_0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf(t70_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X2 @ X3)
% 0.20/0.49          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X5)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X9)
% 0.20/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.20/0.49          | (r1_tsep_1 @ X10 @ X9)
% 0.20/0.49          | ~ (l1_struct_0 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '38'])).
% 0.20/0.49  thf('40', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '41'])).
% 0.20/0.49  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i]:
% 0.20/0.49         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.49  thf('45', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.49  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['42', '47'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['48', '50'])).
% 0.20/0.49  thf('52', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('53', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('54', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('55', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('56', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('57', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('58', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('59', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['4'])).
% 0.20/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X11)
% 0.20/0.49          | ~ (l1_struct_0 @ X12)
% 0.20/0.49          | (r1_tsep_1 @ X12 @ X11)
% 0.20/0.49          | ~ (r1_tsep_1 @ X11 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      ((((r1_tsep_1 @ sk_D @ sk_C)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_tsep_1 @ sk_D @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['59', '62'])).
% 0.20/0.49  thf('64', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.49  thf('66', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['58', '65'])).
% 0.20/0.49  thf('67', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X9)
% 0.20/0.49          | ~ (r1_tsep_1 @ X10 @ X9)
% 0.20/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.20/0.49          | ~ (l1_struct_0 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.49  thf('71', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['57', '70'])).
% 0.20/0.49  thf('72', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('73', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.49  thf('74', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_C)
% 0.20/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['56', '73'])).
% 0.20/0.49  thf('75', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('76', plain,
% 0.20/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['74', '75'])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.49          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X9)
% 0.20/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9))
% 0.20/0.49          | (r1_tsep_1 @ X10 @ X9)
% 0.20/0.49          | ~ (l1_struct_0 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.49  thf('81', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['55', '80'])).
% 0.20/0.49  thf('82', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('83', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['81', '82'])).
% 0.20/0.49  thf('84', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['54', '83'])).
% 0.20/0.49  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('86', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.49  thf('87', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X11)
% 0.20/0.49          | ~ (l1_struct_0 @ X12)
% 0.20/0.49          | (r1_tsep_1 @ X12 @ X11)
% 0.20/0.49          | ~ (r1_tsep_1 @ X11 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.49  thf('88', plain,
% 0.20/0.49      ((((r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.49  thf('89', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['53', '88'])).
% 0.20/0.49  thf('90', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('91', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['89', '90'])).
% 0.20/0.49  thf('92', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['52', '91'])).
% 0.20/0.49  thf('93', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('94', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['92', '93'])).
% 0.20/0.49  thf('95', plain,
% 0.20/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['49'])).
% 0.20/0.49  thf('96', plain,
% 0.20/0.49      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.49  thf('97', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('98', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.49  thf('99', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['42', '47'])).
% 0.20/0.49  thf('100', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (l1_struct_0 @ X11)
% 0.20/0.49          | ~ (l1_struct_0 @ X12)
% 0.20/0.49          | (r1_tsep_1 @ X12 @ X11)
% 0.20/0.49          | ~ (r1_tsep_1 @ X11 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.49  thf('101', plain,
% 0.20/0.49      ((((r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.49  thf('102', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.49         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.49         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['98', '101'])).
% 0.20/0.49  thf('103', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('104', plain,
% 0.20/0.49      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['102', '103'])).
% 0.20/0.49  thf('105', plain,
% 0.20/0.49      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.49         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['97', '104'])).
% 0.20/0.49  thf('106', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('107', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['105', '106'])).
% 0.20/0.49  thf('108', plain,
% 0.20/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['49'])).
% 0.20/0.49  thf('109', plain,
% 0.20/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['107', '108'])).
% 0.20/0.49  thf('110', plain,
% 0.20/0.49      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.49      inference('split', [status(esa)], ['49'])).
% 0.20/0.49  thf('111', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.20/0.49      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.49  thf('112', plain,
% 0.20/0.49      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.49      inference('split', [status(esa)], ['49'])).
% 0.20/0.49  thf('113', plain,
% 0.20/0.49      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['111', '112'])).
% 0.20/0.49  thf('114', plain,
% 0.20/0.49      (((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.20/0.49      inference('split', [status(esa)], ['4'])).
% 0.20/0.49  thf('115', plain, ($false),
% 0.20/0.49      inference('sat_resolution*', [status(thm)],
% 0.20/0.49                ['51', '96', '109', '110', '113', '114'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
