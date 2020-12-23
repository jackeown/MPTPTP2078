%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nBvgijiCPW

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:33 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  261 (2161 expanded)
%              Number of leaves         :   24 ( 604 expanded)
%              Depth                    :   41
%              Number of atoms          : 2748 (48863 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_tsep_1_type,type,(
    k2_tsep_1: $i > $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t41_tmap_1,conjecture,(
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
                 => ( ~ ( r1_tsep_1 @ B @ C )
                   => ( ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D )
                       => ( ~ ( r1_tsep_1 @ B @ D )
                          & ~ ( r1_tsep_1 @ C @ D ) ) )
                      & ( ~ ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) )
                       => ( ~ ( r1_tsep_1 @ D @ B )
                          & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) )).

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
                   => ( ~ ( r1_tsep_1 @ B @ C )
                     => ( ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D )
                         => ( ~ ( r1_tsep_1 @ B @ D )
                            & ~ ( r1_tsep_1 @ C @ D ) ) )
                        & ( ~ ( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) )
                         => ( ~ ( r1_tsep_1 @ D @ B )
                            & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X9 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tsep_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( l1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('15',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['15'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('18',plain,
    ( ( ( r1_tsep_1 @ sk_C @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['18','25','32'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X6 )
      | ~ ( r1_tsep_1 @ X7 @ X6 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('35',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('37',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('38',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tsep_1,axiom,(
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
             => ( ~ ( r1_tsep_1 @ B @ C )
               => ( ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ B )
                  & ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ C ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( r1_tsep_1 @ X13 @ X15 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X14 @ X13 @ X15 ) @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t30_tsep_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ X0 )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

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

thf('48',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( r1_tarski @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['55'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['38','58'])).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X6 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ( r1_tsep_1 @ X7 @ X6 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['14','63'])).

thf('65',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('69',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('73',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('74',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X6 )
      | ~ ( r1_tsep_1 @ X7 @ X6 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('75',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['23','24'])).

thf('77',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('78',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('80',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X6 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ( r1_tsep_1 @ X7 @ X6 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('82',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('84',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['72','84'])).

thf('86',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['87'])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_C @ sk_D ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('100',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('101',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('102',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('109',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('111',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['102','109','110'])).

thf('112',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X6 )
      | ~ ( r1_tsep_1 @ X7 @ X6 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('113',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['107','108'])).

thf('115',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('116',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( r1_tsep_1 @ X13 @ X15 )
      | ( m1_pre_topc @ ( k2_tsep_1 @ X14 @ X13 @ X15 ) @ X13 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t30_tsep_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ X0 ) @ sk_B )
      | ( r1_tsep_1 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['117','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['116','131'])).

thf('133',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X6 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ( r1_tsep_1 @ X7 @ X6 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('136',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['99','136'])).

thf('138',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('140',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('142',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['98','142'])).

thf('144',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['70'])).

thf('146',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_D @ sk_B ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('156',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('157',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['107','108'])).

thf('158',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('159',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X6 )
      | ~ ( r1_tsep_1 @ X7 @ X6 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('160',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['157','160'])).

thf('162',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('163',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('165',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_struct_0 @ X6 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X6 ) )
      | ( r1_tsep_1 @ X7 @ X6 )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('167',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('169',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['156','169'])).

thf('171',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('173',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('175',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['155','175'])).

thf('177',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['70'])).

thf('179',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['170'])).

thf('189',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
   <= ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['87'])).

thf('190',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      & ( r1_tsep_1 @ sk_B @ sk_D ) ) ),
    inference(clc,[status(thm)],['194','195'])).

thf('197',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(split,[status(esa)],['199'])).

thf('201',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('202',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['85'])).

thf('203',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ~ ( l1_struct_0 @ X12 )
      | ( r1_tsep_1 @ X12 @ X11 )
      | ~ ( r1_tsep_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('204',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('206',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tsep_1 @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['201','206'])).

thf('208',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C )
      | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['70'])).

thf('210',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['70'])).

thf('211',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['210','187','198','200','97'])).

thf('212',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['209','211'])).

thf('213',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['208','212'])).

thf('214',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['215','216'])).

thf('218',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['217','218'])).

thf('220',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('223',plain,(
    r1_tsep_1 @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['71','97','154','187','198','200','221','222'])).

thf('224',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( l1_struct_0 @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['69','223'])).

thf('225',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tsep_1 @ sk_B @ sk_C )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','224'])).

thf('226',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C )
    | ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ~ ( r1_tsep_1 @ sk_D @ ( k2_tsep_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['209','211'])).

thf('228',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['230','231'])).

thf('233',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,(
    $false ),
    inference(demod,[status(thm)],['0','234'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nBvgijiCPW
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:27:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.20/1.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.41  % Solved by: fo/fo7.sh
% 1.20/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.41  % done 740 iterations in 0.965s
% 1.20/1.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.41  % SZS output start Refutation
% 1.20/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.41  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.20/1.41  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.20/1.41  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.20/1.41  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.20/1.41  thf(sk_D_type, type, sk_D: $i).
% 1.20/1.41  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.20/1.41  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.41  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.20/1.41  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.20/1.41  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.20/1.41  thf(k2_tsep_1_type, type, k2_tsep_1: $i > $i > $i > $i).
% 1.20/1.41  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 1.20/1.41  thf(sk_C_type, type, sk_C: $i).
% 1.20/1.41  thf(t41_tmap_1, conjecture,
% 1.20/1.42    (![A:$i]:
% 1.20/1.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.20/1.42       ( ![B:$i]:
% 1.20/1.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.20/1.42           ( ![C:$i]:
% 1.20/1.42             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.20/1.42               ( ![D:$i]:
% 1.20/1.42                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.20/1.42                   ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.20/1.42                     ( ( ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) =>
% 1.20/1.42                         ( ( ~( r1_tsep_1 @ B @ D ) ) & 
% 1.20/1.42                           ( ~( r1_tsep_1 @ C @ D ) ) ) ) & 
% 1.20/1.42                       ( ( ~( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 1.20/1.42                         ( ( ~( r1_tsep_1 @ D @ B ) ) & 
% 1.20/1.42                           ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.20/1.42  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.42    (~( ![A:$i]:
% 1.20/1.42        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.20/1.42            ( l1_pre_topc @ A ) ) =>
% 1.20/1.42          ( ![B:$i]:
% 1.20/1.42            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.20/1.42              ( ![C:$i]:
% 1.20/1.42                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.20/1.42                  ( ![D:$i]:
% 1.20/1.42                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 1.20/1.42                      ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.20/1.42                        ( ( ( ~( r1_tsep_1 @ ( k2_tsep_1 @ A @ B @ C ) @ D ) ) =>
% 1.20/1.42                            ( ( ~( r1_tsep_1 @ B @ D ) ) & 
% 1.20/1.42                              ( ~( r1_tsep_1 @ C @ D ) ) ) ) & 
% 1.20/1.42                          ( ( ~( r1_tsep_1 @ D @ ( k2_tsep_1 @ A @ B @ C ) ) ) =>
% 1.20/1.42                            ( ( ~( r1_tsep_1 @ D @ B ) ) & 
% 1.20/1.42                              ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.20/1.42    inference('cnf.neg', [status(esa)], [t41_tmap_1])).
% 1.20/1.42  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('1', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf(dt_k2_tsep_1, axiom,
% 1.20/1.42    (![A:$i,B:$i,C:$i]:
% 1.20/1.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.20/1.42         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 1.20/1.42         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.20/1.42       ( ( ~( v2_struct_0 @ ( k2_tsep_1 @ A @ B @ C ) ) ) & 
% 1.20/1.42         ( v1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) ) & 
% 1.20/1.42         ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 1.20/1.42  thf('3', plain,
% 1.20/1.42      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.20/1.42         (~ (m1_pre_topc @ X8 @ X9)
% 1.20/1.42          | (v2_struct_0 @ X8)
% 1.20/1.42          | ~ (l1_pre_topc @ X9)
% 1.20/1.42          | (v2_struct_0 @ X9)
% 1.20/1.42          | (v2_struct_0 @ X10)
% 1.20/1.42          | ~ (m1_pre_topc @ X10 @ X9)
% 1.20/1.42          | (m1_pre_topc @ (k2_tsep_1 @ X9 @ X8 @ X10) @ X9))),
% 1.20/1.42      inference('cnf', [status(esa)], [dt_k2_tsep_1])).
% 1.20/1.42  thf('4', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.20/1.42          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ X0)
% 1.20/1.42          | (v2_struct_0 @ sk_A)
% 1.20/1.42          | ~ (l1_pre_topc @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ sk_B))),
% 1.20/1.42      inference('sup-', [status(thm)], ['2', '3'])).
% 1.20/1.42  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('6', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_A)
% 1.20/1.42          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ X0)
% 1.20/1.42          | (v2_struct_0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ sk_B))),
% 1.20/1.42      inference('demod', [status(thm)], ['4', '5'])).
% 1.20/1.42  thf('7', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.20/1.42      inference('sup-', [status(thm)], ['1', '6'])).
% 1.20/1.42  thf(dt_m1_pre_topc, axiom,
% 1.20/1.42    (![A:$i]:
% 1.20/1.42     ( ( l1_pre_topc @ A ) =>
% 1.20/1.42       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.20/1.42  thf('8', plain,
% 1.20/1.42      (![X4 : $i, X5 : $i]:
% 1.20/1.42         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 1.20/1.42      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.20/1.42  thf('9', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | ~ (l1_pre_topc @ sk_A)
% 1.20/1.42        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['7', '8'])).
% 1.20/1.42  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('11', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (l1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.20/1.42      inference('demod', [status(thm)], ['9', '10'])).
% 1.20/1.42  thf(dt_l1_pre_topc, axiom,
% 1.20/1.42    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.20/1.42  thf('12', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 1.20/1.42      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.20/1.42  thf('13', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['11', '12'])).
% 1.20/1.42  thf('14', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['11', '12'])).
% 1.20/1.42  thf('15', plain,
% 1.20/1.42      (((r1_tsep_1 @ sk_C @ sk_D)
% 1.20/1.42        | (r1_tsep_1 @ sk_B @ sk_D)
% 1.20/1.42        | (r1_tsep_1 @ sk_D @ sk_B)
% 1.20/1.42        | (r1_tsep_1 @ sk_D @ sk_C))),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('16', plain,
% 1.20/1.42      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('split', [status(esa)], ['15'])).
% 1.20/1.42  thf(symmetry_r1_tsep_1, axiom,
% 1.20/1.42    (![A:$i,B:$i]:
% 1.20/1.42     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 1.20/1.42       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 1.20/1.42  thf('17', plain,
% 1.20/1.42      (![X11 : $i, X12 : $i]:
% 1.20/1.42         (~ (l1_struct_0 @ X11)
% 1.20/1.42          | ~ (l1_struct_0 @ X12)
% 1.20/1.42          | (r1_tsep_1 @ X12 @ X11)
% 1.20/1.42          | ~ (r1_tsep_1 @ X11 @ X12))),
% 1.20/1.42      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.20/1.42  thf('18', plain,
% 1.20/1.42      ((((r1_tsep_1 @ sk_C @ sk_D)
% 1.20/1.42         | ~ (l1_struct_0 @ sk_C)
% 1.20/1.42         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['16', '17'])).
% 1.20/1.42  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('20', plain,
% 1.20/1.42      (![X4 : $i, X5 : $i]:
% 1.20/1.42         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 1.20/1.42      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.20/1.42  thf('21', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 1.20/1.42      inference('sup-', [status(thm)], ['19', '20'])).
% 1.20/1.42  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('23', plain, ((l1_pre_topc @ sk_C)),
% 1.20/1.42      inference('demod', [status(thm)], ['21', '22'])).
% 1.20/1.42  thf('24', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 1.20/1.42      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.20/1.42  thf('25', plain, ((l1_struct_0 @ sk_C)),
% 1.20/1.42      inference('sup-', [status(thm)], ['23', '24'])).
% 1.20/1.42  thf('26', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('27', plain,
% 1.20/1.42      (![X4 : $i, X5 : $i]:
% 1.20/1.42         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 1.20/1.42      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.20/1.42  thf('28', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 1.20/1.42      inference('sup-', [status(thm)], ['26', '27'])).
% 1.20/1.42  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('30', plain, ((l1_pre_topc @ sk_D)),
% 1.20/1.42      inference('demod', [status(thm)], ['28', '29'])).
% 1.20/1.42  thf('31', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 1.20/1.42      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.20/1.42  thf('32', plain, ((l1_struct_0 @ sk_D)),
% 1.20/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.20/1.42  thf('33', plain,
% 1.20/1.42      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('demod', [status(thm)], ['18', '25', '32'])).
% 1.20/1.42  thf(d3_tsep_1, axiom,
% 1.20/1.42    (![A:$i]:
% 1.20/1.42     ( ( l1_struct_0 @ A ) =>
% 1.20/1.42       ( ![B:$i]:
% 1.20/1.42         ( ( l1_struct_0 @ B ) =>
% 1.20/1.42           ( ( r1_tsep_1 @ A @ B ) <=>
% 1.20/1.42             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.20/1.42  thf('34', plain,
% 1.20/1.42      (![X6 : $i, X7 : $i]:
% 1.20/1.42         (~ (l1_struct_0 @ X6)
% 1.20/1.42          | ~ (r1_tsep_1 @ X7 @ X6)
% 1.20/1.42          | (r1_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 1.20/1.42          | ~ (l1_struct_0 @ X7))),
% 1.20/1.42      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.20/1.42  thf('35', plain,
% 1.20/1.42      (((~ (l1_struct_0 @ sk_C)
% 1.20/1.42         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 1.20/1.42         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['33', '34'])).
% 1.20/1.42  thf('36', plain, ((l1_struct_0 @ sk_C)),
% 1.20/1.42      inference('sup-', [status(thm)], ['23', '24'])).
% 1.20/1.42  thf('37', plain, ((l1_struct_0 @ sk_D)),
% 1.20/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.20/1.42  thf('38', plain,
% 1.20/1.42      (((r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 1.20/1.42         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('demod', [status(thm)], ['35', '36', '37'])).
% 1.20/1.42  thf('39', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf(t30_tsep_1, axiom,
% 1.20/1.42    (![A:$i]:
% 1.20/1.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.20/1.42       ( ![B:$i]:
% 1.20/1.42         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.20/1.42           ( ![C:$i]:
% 1.20/1.42             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.20/1.42               ( ( ~( r1_tsep_1 @ B @ C ) ) =>
% 1.20/1.42                 ( ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ B ) & 
% 1.20/1.42                   ( m1_pre_topc @ ( k2_tsep_1 @ A @ B @ C ) @ C ) ) ) ) ) ) ) ))).
% 1.20/1.42  thf('41', plain,
% 1.20/1.42      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.20/1.42         ((v2_struct_0 @ X13)
% 1.20/1.42          | ~ (m1_pre_topc @ X13 @ X14)
% 1.20/1.42          | (r1_tsep_1 @ X13 @ X15)
% 1.20/1.42          | (m1_pre_topc @ (k2_tsep_1 @ X14 @ X13 @ X15) @ X15)
% 1.20/1.42          | ~ (m1_pre_topc @ X15 @ X14)
% 1.20/1.42          | (v2_struct_0 @ X15)
% 1.20/1.42          | ~ (l1_pre_topc @ X14)
% 1.20/1.42          | ~ (v2_pre_topc @ X14)
% 1.20/1.42          | (v2_struct_0 @ X14))),
% 1.20/1.42      inference('cnf', [status(esa)], [t30_tsep_1])).
% 1.20/1.42  thf('42', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((v2_struct_0 @ sk_A)
% 1.20/1.42          | ~ (v2_pre_topc @ sk_A)
% 1.20/1.42          | ~ (l1_pre_topc @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ X0)
% 1.20/1.42          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.20/1.42          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ X0)
% 1.20/1.42          | (r1_tsep_1 @ sk_B @ X0)
% 1.20/1.42          | (v2_struct_0 @ sk_B))),
% 1.20/1.42      inference('sup-', [status(thm)], ['40', '41'])).
% 1.20/1.42  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('45', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((v2_struct_0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ X0)
% 1.20/1.42          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.20/1.42          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ X0)
% 1.20/1.42          | (r1_tsep_1 @ sk_B @ X0)
% 1.20/1.42          | (v2_struct_0 @ sk_B))),
% 1.20/1.42      inference('demod', [status(thm)], ['42', '43', '44'])).
% 1.20/1.42  thf('46', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_B)
% 1.20/1.42        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_A))),
% 1.20/1.42      inference('sup-', [status(thm)], ['39', '45'])).
% 1.20/1.42  thf('47', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 1.20/1.42      inference('sup-', [status(thm)], ['1', '6'])).
% 1.20/1.42  thf(t4_tsep_1, axiom,
% 1.20/1.42    (![A:$i]:
% 1.20/1.42     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.20/1.42       ( ![B:$i]:
% 1.20/1.42         ( ( m1_pre_topc @ B @ A ) =>
% 1.20/1.42           ( ![C:$i]:
% 1.20/1.42             ( ( m1_pre_topc @ C @ A ) =>
% 1.20/1.42               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 1.20/1.42                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 1.20/1.42  thf('48', plain,
% 1.20/1.42      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.20/1.42         (~ (m1_pre_topc @ X16 @ X17)
% 1.20/1.42          | ~ (m1_pre_topc @ X16 @ X18)
% 1.20/1.42          | (r1_tarski @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X18))
% 1.20/1.42          | ~ (m1_pre_topc @ X18 @ X17)
% 1.20/1.42          | ~ (l1_pre_topc @ X17)
% 1.20/1.42          | ~ (v2_pre_topc @ X17))),
% 1.20/1.42      inference('cnf', [status(esa)], [t4_tsep_1])).
% 1.20/1.42  thf('49', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((v2_struct_0 @ sk_C)
% 1.20/1.42          | (v2_struct_0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ sk_B)
% 1.20/1.42          | ~ (v2_pre_topc @ sk_A)
% 1.20/1.42          | ~ (l1_pre_topc @ sk_A)
% 1.20/1.42          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.20/1.42          | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42             (u1_struct_0 @ X0))
% 1.20/1.42          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0))),
% 1.20/1.42      inference('sup-', [status(thm)], ['47', '48'])).
% 1.20/1.42  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('52', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((v2_struct_0 @ sk_C)
% 1.20/1.42          | (v2_struct_0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ sk_B)
% 1.20/1.42          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.20/1.42          | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42             (u1_struct_0 @ X0))
% 1.20/1.42          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0))),
% 1.20/1.42      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.20/1.42  thf('53', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42           (u1_struct_0 @ sk_C))
% 1.20/1.42        | ~ (m1_pre_topc @ sk_C @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C))),
% 1.20/1.42      inference('sup-', [status(thm)], ['46', '52'])).
% 1.20/1.42  thf('54', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('55', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42           (u1_struct_0 @ sk_C))
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C))),
% 1.20/1.42      inference('demod', [status(thm)], ['53', '54'])).
% 1.20/1.42  thf('56', plain,
% 1.20/1.42      (((r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42         (u1_struct_0 @ sk_C))
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_A))),
% 1.20/1.42      inference('simplify', [status(thm)], ['55'])).
% 1.20/1.42  thf(t63_xboole_1, axiom,
% 1.20/1.42    (![A:$i,B:$i,C:$i]:
% 1.20/1.42     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.20/1.42       ( r1_xboole_0 @ A @ C ) ))).
% 1.20/1.42  thf('57', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.42         (~ (r1_tarski @ X0 @ X1)
% 1.20/1.42          | ~ (r1_xboole_0 @ X1 @ X2)
% 1.20/1.42          | (r1_xboole_0 @ X0 @ X2))),
% 1.20/1.42      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.20/1.42  thf('58', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((v2_struct_0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ sk_C)
% 1.20/1.42          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42          | (v2_struct_0 @ sk_B)
% 1.20/1.42          | (r1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42             X0)
% 1.20/1.42          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ X0))),
% 1.20/1.42      inference('sup-', [status(thm)], ['56', '57'])).
% 1.20/1.42  thf('59', plain,
% 1.20/1.42      ((((r1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42          (u1_struct_0 @ sk_D))
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['38', '58'])).
% 1.20/1.42  thf('60', plain,
% 1.20/1.42      (![X6 : $i, X7 : $i]:
% 1.20/1.42         (~ (l1_struct_0 @ X6)
% 1.20/1.42          | ~ (r1_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 1.20/1.42          | (r1_tsep_1 @ X7 @ X6)
% 1.20/1.42          | ~ (l1_struct_0 @ X7))),
% 1.20/1.42      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.20/1.42  thf('61', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_C)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.20/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.20/1.42         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['59', '60'])).
% 1.20/1.42  thf('62', plain, ((l1_struct_0 @ sk_D)),
% 1.20/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.20/1.42  thf('63', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_C)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.20/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))
% 1.20/1.42         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('demod', [status(thm)], ['61', '62'])).
% 1.20/1.42  thf('64', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['14', '63'])).
% 1.20/1.42  thf('65', plain,
% 1.20/1.42      ((((r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('simplify', [status(thm)], ['64'])).
% 1.20/1.42  thf('66', plain,
% 1.20/1.42      (![X11 : $i, X12 : $i]:
% 1.20/1.42         (~ (l1_struct_0 @ X11)
% 1.20/1.42          | ~ (l1_struct_0 @ X12)
% 1.20/1.42          | (r1_tsep_1 @ X12 @ X11)
% 1.20/1.42          | ~ (r1_tsep_1 @ X11 @ X12))),
% 1.20/1.42      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.20/1.42  thf('67', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.20/1.42         | ~ (l1_struct_0 @ sk_D)
% 1.20/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.20/1.42         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['65', '66'])).
% 1.20/1.42  thf('68', plain, ((l1_struct_0 @ sk_D)),
% 1.20/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.20/1.42  thf('69', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.20/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.20/1.42         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 1.20/1.42      inference('demod', [status(thm)], ['67', '68'])).
% 1.20/1.42  thf('70', plain,
% 1.20/1.42      (((r1_tsep_1 @ sk_C @ sk_D)
% 1.20/1.42        | (r1_tsep_1 @ sk_B @ sk_D)
% 1.20/1.42        | ~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('71', plain,
% 1.20/1.42      (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.20/1.42       ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 1.20/1.42      inference('split', [status(esa)], ['70'])).
% 1.20/1.42  thf('72', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['11', '12'])).
% 1.20/1.42  thf('73', plain,
% 1.20/1.42      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('split', [status(esa)], ['15'])).
% 1.20/1.42  thf('74', plain,
% 1.20/1.42      (![X6 : $i, X7 : $i]:
% 1.20/1.42         (~ (l1_struct_0 @ X6)
% 1.20/1.42          | ~ (r1_tsep_1 @ X7 @ X6)
% 1.20/1.42          | (r1_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 1.20/1.42          | ~ (l1_struct_0 @ X7))),
% 1.20/1.42      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.20/1.42  thf('75', plain,
% 1.20/1.42      (((~ (l1_struct_0 @ sk_C)
% 1.20/1.42         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 1.20/1.42         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['73', '74'])).
% 1.20/1.42  thf('76', plain, ((l1_struct_0 @ sk_C)),
% 1.20/1.42      inference('sup-', [status(thm)], ['23', '24'])).
% 1.20/1.42  thf('77', plain, ((l1_struct_0 @ sk_D)),
% 1.20/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.20/1.42  thf('78', plain,
% 1.20/1.42      (((r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 1.20/1.42         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.20/1.42  thf('79', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((v2_struct_0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ sk_C)
% 1.20/1.42          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42          | (v2_struct_0 @ sk_B)
% 1.20/1.42          | (r1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42             X0)
% 1.20/1.42          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ X0))),
% 1.20/1.42      inference('sup-', [status(thm)], ['56', '57'])).
% 1.20/1.42  thf('80', plain,
% 1.20/1.42      ((((r1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42          (u1_struct_0 @ sk_D))
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['78', '79'])).
% 1.20/1.42  thf('81', plain,
% 1.20/1.42      (![X6 : $i, X7 : $i]:
% 1.20/1.42         (~ (l1_struct_0 @ X6)
% 1.20/1.42          | ~ (r1_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 1.20/1.42          | (r1_tsep_1 @ X7 @ X6)
% 1.20/1.42          | ~ (l1_struct_0 @ X7))),
% 1.20/1.42      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.20/1.42  thf('82', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_C)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.20/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.20/1.42         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['80', '81'])).
% 1.20/1.42  thf('83', plain, ((l1_struct_0 @ sk_D)),
% 1.20/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.20/1.42  thf('84', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_C)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.20/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))
% 1.20/1.42         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('demod', [status(thm)], ['82', '83'])).
% 1.20/1.42  thf('85', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['72', '84'])).
% 1.20/1.42  thf('86', plain,
% 1.20/1.42      ((((r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('simplify', [status(thm)], ['85'])).
% 1.20/1.42  thf('87', plain,
% 1.20/1.42      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.20/1.42        | (r1_tsep_1 @ sk_D @ sk_B)
% 1.20/1.42        | (r1_tsep_1 @ sk_D @ sk_C))),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('88', plain,
% 1.20/1.42      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 1.20/1.42         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.20/1.42      inference('split', [status(esa)], ['87'])).
% 1.20/1.42  thf('89', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_A)
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)))
% 1.20/1.42         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.20/1.42             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['86', '88'])).
% 1.20/1.42  thf('90', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('91', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.20/1.42         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.20/1.42             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['89', '90'])).
% 1.20/1.42  thf('92', plain, (~ (v2_struct_0 @ sk_B)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('93', plain,
% 1.20/1.42      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.20/1.42         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.20/1.42             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('clc', [status(thm)], ['91', '92'])).
% 1.20/1.42  thf('94', plain, (~ (v2_struct_0 @ sk_C)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('95', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_A))
% 1.20/1.42         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.20/1.42             ((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.20/1.42      inference('clc', [status(thm)], ['93', '94'])).
% 1.20/1.42  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('97', plain,
% 1.20/1.42      (((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) | 
% 1.20/1.42       ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 1.20/1.42      inference('sup-', [status(thm)], ['95', '96'])).
% 1.20/1.42  thf('98', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['11', '12'])).
% 1.20/1.42  thf('99', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['11', '12'])).
% 1.20/1.42  thf('100', plain,
% 1.20/1.42      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.20/1.42      inference('split', [status(esa)], ['15'])).
% 1.20/1.42  thf('101', plain,
% 1.20/1.42      (![X11 : $i, X12 : $i]:
% 1.20/1.42         (~ (l1_struct_0 @ X11)
% 1.20/1.42          | ~ (l1_struct_0 @ X12)
% 1.20/1.42          | (r1_tsep_1 @ X12 @ X11)
% 1.20/1.42          | ~ (r1_tsep_1 @ X11 @ X12))),
% 1.20/1.42      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.20/1.42  thf('102', plain,
% 1.20/1.42      ((((r1_tsep_1 @ sk_B @ sk_D)
% 1.20/1.42         | ~ (l1_struct_0 @ sk_B)
% 1.20/1.42         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['100', '101'])).
% 1.20/1.42  thf('103', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('104', plain,
% 1.20/1.42      (![X4 : $i, X5 : $i]:
% 1.20/1.42         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 1.20/1.42      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.20/1.42  thf('105', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 1.20/1.42      inference('sup-', [status(thm)], ['103', '104'])).
% 1.20/1.42  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('107', plain, ((l1_pre_topc @ sk_B)),
% 1.20/1.42      inference('demod', [status(thm)], ['105', '106'])).
% 1.20/1.42  thf('108', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 1.20/1.42      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.20/1.42  thf('109', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.42      inference('sup-', [status(thm)], ['107', '108'])).
% 1.20/1.42  thf('110', plain, ((l1_struct_0 @ sk_D)),
% 1.20/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.20/1.42  thf('111', plain,
% 1.20/1.42      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.20/1.42      inference('demod', [status(thm)], ['102', '109', '110'])).
% 1.20/1.42  thf('112', plain,
% 1.20/1.42      (![X6 : $i, X7 : $i]:
% 1.20/1.42         (~ (l1_struct_0 @ X6)
% 1.20/1.42          | ~ (r1_tsep_1 @ X7 @ X6)
% 1.20/1.42          | (r1_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 1.20/1.42          | ~ (l1_struct_0 @ X7))),
% 1.20/1.42      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.20/1.42  thf('113', plain,
% 1.20/1.42      (((~ (l1_struct_0 @ sk_B)
% 1.20/1.42         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))
% 1.20/1.42         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['111', '112'])).
% 1.20/1.42  thf('114', plain, ((l1_struct_0 @ sk_B)),
% 1.20/1.42      inference('sup-', [status(thm)], ['107', '108'])).
% 1.20/1.42  thf('115', plain, ((l1_struct_0 @ sk_D)),
% 1.20/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.20/1.42  thf('116', plain,
% 1.20/1.42      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 1.20/1.42         <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.20/1.42      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.20/1.42  thf('117', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('118', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('119', plain,
% 1.20/1.42      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.20/1.42         ((v2_struct_0 @ X13)
% 1.20/1.42          | ~ (m1_pre_topc @ X13 @ X14)
% 1.20/1.42          | (r1_tsep_1 @ X13 @ X15)
% 1.20/1.42          | (m1_pre_topc @ (k2_tsep_1 @ X14 @ X13 @ X15) @ X13)
% 1.20/1.42          | ~ (m1_pre_topc @ X15 @ X14)
% 1.20/1.42          | (v2_struct_0 @ X15)
% 1.20/1.42          | ~ (l1_pre_topc @ X14)
% 1.20/1.42          | ~ (v2_pre_topc @ X14)
% 1.20/1.42          | (v2_struct_0 @ X14))),
% 1.20/1.42      inference('cnf', [status(esa)], [t30_tsep_1])).
% 1.20/1.42  thf('120', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((v2_struct_0 @ sk_A)
% 1.20/1.42          | ~ (v2_pre_topc @ sk_A)
% 1.20/1.42          | ~ (l1_pre_topc @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ X0)
% 1.20/1.42          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.20/1.42          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B)
% 1.20/1.42          | (r1_tsep_1 @ sk_B @ X0)
% 1.20/1.42          | (v2_struct_0 @ sk_B))),
% 1.20/1.42      inference('sup-', [status(thm)], ['118', '119'])).
% 1.20/1.42  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('123', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((v2_struct_0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ X0)
% 1.20/1.42          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.20/1.42          | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ X0) @ sk_B)
% 1.20/1.42          | (r1_tsep_1 @ sk_B @ X0)
% 1.20/1.42          | (v2_struct_0 @ sk_B))),
% 1.20/1.42      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.20/1.42  thf('124', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_B)
% 1.20/1.42        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42        | (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_A))),
% 1.20/1.42      inference('sup-', [status(thm)], ['117', '123'])).
% 1.20/1.42  thf('125', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((v2_struct_0 @ sk_C)
% 1.20/1.42          | (v2_struct_0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ sk_B)
% 1.20/1.42          | ~ (m1_pre_topc @ X0 @ sk_A)
% 1.20/1.42          | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42             (u1_struct_0 @ X0))
% 1.20/1.42          | ~ (m1_pre_topc @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ X0))),
% 1.20/1.42      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.20/1.42  thf('126', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42           (u1_struct_0 @ sk_B))
% 1.20/1.42        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C))),
% 1.20/1.42      inference('sup-', [status(thm)], ['124', '125'])).
% 1.20/1.42  thf('127', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 1.20/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.42  thf('128', plain,
% 1.20/1.42      (((v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42           (u1_struct_0 @ sk_B))
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (v2_struct_0 @ sk_A)
% 1.20/1.42        | (v2_struct_0 @ sk_C))),
% 1.20/1.42      inference('demod', [status(thm)], ['126', '127'])).
% 1.20/1.42  thf('129', plain,
% 1.20/1.42      (((r1_tarski @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42         (u1_struct_0 @ sk_B))
% 1.20/1.42        | (v2_struct_0 @ sk_B)
% 1.20/1.42        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_C)
% 1.20/1.42        | (v2_struct_0 @ sk_A))),
% 1.20/1.42      inference('simplify', [status(thm)], ['128'])).
% 1.20/1.42  thf('130', plain,
% 1.20/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.42         (~ (r1_tarski @ X0 @ X1)
% 1.20/1.42          | ~ (r1_xboole_0 @ X1 @ X2)
% 1.20/1.42          | (r1_xboole_0 @ X0 @ X2))),
% 1.20/1.42      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.20/1.42  thf('131', plain,
% 1.20/1.42      (![X0 : $i]:
% 1.20/1.42         ((v2_struct_0 @ sk_A)
% 1.20/1.42          | (v2_struct_0 @ sk_C)
% 1.20/1.42          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42          | (v2_struct_0 @ sk_B)
% 1.20/1.42          | (r1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42             X0)
% 1.20/1.42          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 1.20/1.42      inference('sup-', [status(thm)], ['129', '130'])).
% 1.20/1.42  thf('132', plain,
% 1.20/1.42      ((((r1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.20/1.42          (u1_struct_0 @ sk_D))
% 1.20/1.42         | (v2_struct_0 @ sk_B)
% 1.20/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_C)
% 1.20/1.42         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.20/1.42      inference('sup-', [status(thm)], ['116', '131'])).
% 1.20/1.42  thf('133', plain,
% 1.20/1.42      (![X6 : $i, X7 : $i]:
% 1.26/1.42         (~ (l1_struct_0 @ X6)
% 1.26/1.42          | ~ (r1_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 1.26/1.42          | (r1_tsep_1 @ X7 @ X6)
% 1.26/1.42          | ~ (l1_struct_0 @ X7))),
% 1.26/1.42      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.26/1.42  thf('134', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.26/1.42         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['132', '133'])).
% 1.26/1.42  thf('135', plain, ((l1_struct_0 @ sk_D)),
% 1.26/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.26/1.42  thf('136', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('demod', [status(thm)], ['134', '135'])).
% 1.26/1.42  thf('137', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['99', '136'])).
% 1.26/1.42  thf('138', plain,
% 1.26/1.42      ((((r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('simplify', [status(thm)], ['137'])).
% 1.26/1.42  thf('139', plain,
% 1.26/1.42      (![X11 : $i, X12 : $i]:
% 1.26/1.42         (~ (l1_struct_0 @ X11)
% 1.26/1.42          | ~ (l1_struct_0 @ X12)
% 1.26/1.42          | (r1_tsep_1 @ X12 @ X11)
% 1.26/1.42          | ~ (r1_tsep_1 @ X11 @ X12))),
% 1.26/1.42      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.26/1.42  thf('140', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | ~ (l1_struct_0 @ sk_D)
% 1.26/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['138', '139'])).
% 1.26/1.42  thf('141', plain, ((l1_struct_0 @ sk_D)),
% 1.26/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.26/1.42  thf('142', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('demod', [status(thm)], ['140', '141'])).
% 1.26/1.42  thf('143', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['98', '142'])).
% 1.26/1.42  thf('144', plain,
% 1.26/1.42      ((((r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('simplify', [status(thm)], ['143'])).
% 1.26/1.42  thf('145', plain,
% 1.26/1.42      ((~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.26/1.42      inference('split', [status(esa)], ['70'])).
% 1.26/1.42  thf('146', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['144', '145'])).
% 1.26/1.42  thf('147', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('148', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['146', '147'])).
% 1.26/1.42  thf('149', plain, (~ (v2_struct_0 @ sk_B)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('150', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('clc', [status(thm)], ['148', '149'])).
% 1.26/1.42  thf('151', plain, (~ (v2_struct_0 @ sk_C)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('152', plain,
% 1.26/1.42      (((v2_struct_0 @ sk_A))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_D @ sk_B)))),
% 1.26/1.42      inference('clc', [status(thm)], ['150', '151'])).
% 1.26/1.42  thf('153', plain, (~ (v2_struct_0 @ sk_A)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('154', plain,
% 1.26/1.42      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | 
% 1.26/1.42       ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['152', '153'])).
% 1.26/1.42  thf('155', plain,
% 1.26/1.42      (((v2_struct_0 @ sk_B)
% 1.26/1.42        | (v2_struct_0 @ sk_A)
% 1.26/1.42        | (v2_struct_0 @ sk_C)
% 1.26/1.42        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['11', '12'])).
% 1.26/1.42  thf('156', plain,
% 1.26/1.42      (((v2_struct_0 @ sk_B)
% 1.26/1.42        | (v2_struct_0 @ sk_A)
% 1.26/1.42        | (v2_struct_0 @ sk_C)
% 1.26/1.42        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['11', '12'])).
% 1.26/1.42  thf('157', plain, ((l1_struct_0 @ sk_B)),
% 1.26/1.42      inference('sup-', [status(thm)], ['107', '108'])).
% 1.26/1.42  thf('158', plain,
% 1.26/1.42      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('split', [status(esa)], ['15'])).
% 1.26/1.42  thf('159', plain,
% 1.26/1.42      (![X6 : $i, X7 : $i]:
% 1.26/1.42         (~ (l1_struct_0 @ X6)
% 1.26/1.42          | ~ (r1_tsep_1 @ X7 @ X6)
% 1.26/1.42          | (r1_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 1.26/1.42          | ~ (l1_struct_0 @ X7))),
% 1.26/1.42      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.26/1.42  thf('160', plain,
% 1.26/1.42      (((~ (l1_struct_0 @ sk_B)
% 1.26/1.42         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))
% 1.26/1.42         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['158', '159'])).
% 1.26/1.42  thf('161', plain,
% 1.26/1.42      (((~ (l1_struct_0 @ sk_D)
% 1.26/1.42         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D))))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['157', '160'])).
% 1.26/1.42  thf('162', plain, ((l1_struct_0 @ sk_D)),
% 1.26/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.26/1.42  thf('163', plain,
% 1.26/1.42      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('demod', [status(thm)], ['161', '162'])).
% 1.26/1.42  thf('164', plain,
% 1.26/1.42      (![X0 : $i]:
% 1.26/1.42         ((v2_struct_0 @ sk_A)
% 1.26/1.42          | (v2_struct_0 @ sk_C)
% 1.26/1.42          | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42          | (v2_struct_0 @ sk_B)
% 1.26/1.42          | (r1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.26/1.42             X0)
% 1.26/1.42          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 1.26/1.42      inference('sup-', [status(thm)], ['129', '130'])).
% 1.26/1.42  thf('165', plain,
% 1.26/1.42      ((((r1_xboole_0 @ (u1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)) @ 
% 1.26/1.42          (u1_struct_0 @ sk_D))
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['163', '164'])).
% 1.26/1.42  thf('166', plain,
% 1.26/1.42      (![X6 : $i, X7 : $i]:
% 1.26/1.42         (~ (l1_struct_0 @ X6)
% 1.26/1.42          | ~ (r1_xboole_0 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X6))
% 1.26/1.42          | (r1_tsep_1 @ X7 @ X6)
% 1.26/1.42          | ~ (l1_struct_0 @ X7))),
% 1.26/1.42      inference('cnf', [status(esa)], [d3_tsep_1])).
% 1.26/1.42  thf('167', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.26/1.42         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['165', '166'])).
% 1.26/1.42  thf('168', plain, ((l1_struct_0 @ sk_D)),
% 1.26/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.26/1.42  thf('169', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('demod', [status(thm)], ['167', '168'])).
% 1.26/1.42  thf('170', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['156', '169'])).
% 1.26/1.42  thf('171', plain,
% 1.26/1.42      ((((r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('simplify', [status(thm)], ['170'])).
% 1.26/1.42  thf('172', plain,
% 1.26/1.42      (![X11 : $i, X12 : $i]:
% 1.26/1.42         (~ (l1_struct_0 @ X11)
% 1.26/1.42          | ~ (l1_struct_0 @ X12)
% 1.26/1.42          | (r1_tsep_1 @ X12 @ X11)
% 1.26/1.42          | ~ (r1_tsep_1 @ X11 @ X12))),
% 1.26/1.42      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.26/1.42  thf('173', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | ~ (l1_struct_0 @ sk_D)
% 1.26/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['171', '172'])).
% 1.26/1.42  thf('174', plain, ((l1_struct_0 @ sk_D)),
% 1.26/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.26/1.42  thf('175', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('demod', [status(thm)], ['173', '174'])).
% 1.26/1.42  thf('176', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['155', '175'])).
% 1.26/1.42  thf('177', plain,
% 1.26/1.42      ((((r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('simplify', [status(thm)], ['176'])).
% 1.26/1.42  thf('178', plain,
% 1.26/1.42      ((~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.26/1.42      inference('split', [status(esa)], ['70'])).
% 1.26/1.42  thf('179', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['177', '178'])).
% 1.26/1.42  thf('180', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('181', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['179', '180'])).
% 1.26/1.42  thf('182', plain, (~ (v2_struct_0 @ sk_B)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('183', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('clc', [status(thm)], ['181', '182'])).
% 1.26/1.42  thf('184', plain, (~ (v2_struct_0 @ sk_C)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('185', plain,
% 1.26/1.42      (((v2_struct_0 @ sk_A))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('clc', [status(thm)], ['183', '184'])).
% 1.26/1.42  thf('186', plain, (~ (v2_struct_0 @ sk_A)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('187', plain,
% 1.26/1.42      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | 
% 1.26/1.42       ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['185', '186'])).
% 1.26/1.42  thf('188', plain,
% 1.26/1.42      ((((r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('simplify', [status(thm)], ['170'])).
% 1.26/1.42  thf('189', plain,
% 1.26/1.42      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)))),
% 1.26/1.42      inference('split', [status(esa)], ['87'])).
% 1.26/1.42  thf('190', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['188', '189'])).
% 1.26/1.42  thf('191', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('192', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['190', '191'])).
% 1.26/1.42  thf('193', plain, (~ (v2_struct_0 @ sk_B)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('194', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('clc', [status(thm)], ['192', '193'])).
% 1.26/1.42  thf('195', plain, (~ (v2_struct_0 @ sk_C)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('196', plain,
% 1.26/1.42      (((v2_struct_0 @ sk_A))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)) & 
% 1.26/1.42             ((r1_tsep_1 @ sk_B @ sk_D)))),
% 1.26/1.42      inference('clc', [status(thm)], ['194', '195'])).
% 1.26/1.42  thf('197', plain, (~ (v2_struct_0 @ sk_A)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('198', plain,
% 1.26/1.42      (~ ((r1_tsep_1 @ sk_B @ sk_D)) | 
% 1.26/1.42       ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 1.26/1.42      inference('sup-', [status(thm)], ['196', '197'])).
% 1.26/1.42  thf('199', plain,
% 1.26/1.42      ((~ (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.26/1.42        | ~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('200', plain,
% 1.26/1.42      (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.26/1.42       ~ ((r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 1.26/1.42      inference('split', [status(esa)], ['199'])).
% 1.26/1.42  thf('201', plain,
% 1.26/1.42      (((v2_struct_0 @ sk_B)
% 1.26/1.42        | (v2_struct_0 @ sk_A)
% 1.26/1.42        | (v2_struct_0 @ sk_C)
% 1.26/1.42        | (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['11', '12'])).
% 1.26/1.42  thf('202', plain,
% 1.26/1.42      ((((r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C) @ sk_D)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.26/1.42      inference('simplify', [status(thm)], ['85'])).
% 1.26/1.42  thf('203', plain,
% 1.26/1.42      (![X11 : $i, X12 : $i]:
% 1.26/1.42         (~ (l1_struct_0 @ X11)
% 1.26/1.42          | ~ (l1_struct_0 @ X12)
% 1.26/1.42          | (r1_tsep_1 @ X12 @ X11)
% 1.26/1.42          | ~ (r1_tsep_1 @ X11 @ X12))),
% 1.26/1.42      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 1.26/1.42  thf('204', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | ~ (l1_struct_0 @ sk_D)
% 1.26/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['202', '203'])).
% 1.26/1.42  thf('205', plain, ((l1_struct_0 @ sk_D)),
% 1.26/1.42      inference('sup-', [status(thm)], ['30', '31'])).
% 1.26/1.42  thf('206', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.26/1.42      inference('demod', [status(thm)], ['204', '205'])).
% 1.26/1.42  thf('207', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['201', '206'])).
% 1.26/1.42  thf('208', plain,
% 1.26/1.42      ((((r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42         | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.26/1.42      inference('simplify', [status(thm)], ['207'])).
% 1.26/1.42  thf('209', plain,
% 1.26/1.42      ((~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))
% 1.26/1.42         <= (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))))),
% 1.26/1.42      inference('split', [status(esa)], ['70'])).
% 1.26/1.42  thf('210', plain,
% 1.26/1.42      (((r1_tsep_1 @ sk_C @ sk_D)) | 
% 1.26/1.42       ~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))) | 
% 1.26/1.42       ((r1_tsep_1 @ sk_B @ sk_D))),
% 1.26/1.42      inference('split', [status(esa)], ['70'])).
% 1.26/1.42  thf('211', plain,
% 1.26/1.42      (~ ((r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.26/1.42      inference('sat_resolution*', [status(thm)],
% 1.26/1.42                ['210', '187', '198', '200', '97'])).
% 1.26/1.42  thf('212', plain, (~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 1.26/1.42      inference('simpl_trail', [status(thm)], ['209', '211'])).
% 1.26/1.42  thf('213', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C)
% 1.26/1.42         | (v2_struct_0 @ sk_A)
% 1.26/1.42         | (v2_struct_0 @ sk_B)
% 1.26/1.42         | (r1_tsep_1 @ sk_B @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['208', '212'])).
% 1.26/1.42  thf('214', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('215', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.26/1.42      inference('sup-', [status(thm)], ['213', '214'])).
% 1.26/1.42  thf('216', plain, (~ (v2_struct_0 @ sk_B)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('217', plain,
% 1.26/1.42      ((((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 1.26/1.42         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.26/1.42      inference('clc', [status(thm)], ['215', '216'])).
% 1.26/1.42  thf('218', plain, (~ (v2_struct_0 @ sk_C)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('219', plain, (((v2_struct_0 @ sk_A)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 1.26/1.42      inference('clc', [status(thm)], ['217', '218'])).
% 1.26/1.42  thf('220', plain, (~ (v2_struct_0 @ sk_A)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('221', plain, (~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 1.26/1.42      inference('sup-', [status(thm)], ['219', '220'])).
% 1.26/1.42  thf('222', plain,
% 1.26/1.42      (((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_C @ sk_D)) | 
% 1.26/1.42       ((r1_tsep_1 @ sk_B @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 1.26/1.42      inference('split', [status(esa)], ['15'])).
% 1.26/1.42  thf('223', plain, (((r1_tsep_1 @ sk_D @ sk_C))),
% 1.26/1.42      inference('sat_resolution*', [status(thm)],
% 1.26/1.42                ['71', '97', '154', '187', '198', '200', '221', '222'])).
% 1.26/1.42  thf('224', plain,
% 1.26/1.42      (((v2_struct_0 @ sk_C)
% 1.26/1.42        | (v2_struct_0 @ sk_A)
% 1.26/1.42        | (v2_struct_0 @ sk_B)
% 1.26/1.42        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42        | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42        | ~ (l1_struct_0 @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C)))),
% 1.26/1.42      inference('simpl_trail', [status(thm)], ['69', '223'])).
% 1.26/1.42  thf('225', plain,
% 1.26/1.42      (((v2_struct_0 @ sk_C)
% 1.26/1.42        | (v2_struct_0 @ sk_A)
% 1.26/1.42        | (v2_struct_0 @ sk_B)
% 1.26/1.42        | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42        | (r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42        | (v2_struct_0 @ sk_B)
% 1.26/1.42        | (v2_struct_0 @ sk_A)
% 1.26/1.42        | (v2_struct_0 @ sk_C))),
% 1.26/1.42      inference('sup-', [status(thm)], ['13', '224'])).
% 1.26/1.42  thf('226', plain,
% 1.26/1.42      (((r1_tsep_1 @ sk_B @ sk_C)
% 1.26/1.42        | (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))
% 1.26/1.42        | (v2_struct_0 @ sk_B)
% 1.26/1.42        | (v2_struct_0 @ sk_A)
% 1.26/1.42        | (v2_struct_0 @ sk_C))),
% 1.26/1.42      inference('simplify', [status(thm)], ['225'])).
% 1.26/1.42  thf('227', plain, (~ (r1_tsep_1 @ sk_D @ (k2_tsep_1 @ sk_A @ sk_B @ sk_C))),
% 1.26/1.42      inference('simpl_trail', [status(thm)], ['209', '211'])).
% 1.26/1.42  thf('228', plain,
% 1.26/1.42      (((v2_struct_0 @ sk_C)
% 1.26/1.42        | (v2_struct_0 @ sk_A)
% 1.26/1.42        | (v2_struct_0 @ sk_B)
% 1.26/1.42        | (r1_tsep_1 @ sk_B @ sk_C))),
% 1.26/1.42      inference('sup-', [status(thm)], ['226', '227'])).
% 1.26/1.42  thf('229', plain, (~ (r1_tsep_1 @ sk_B @ sk_C)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('230', plain,
% 1.26/1.42      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 1.26/1.42      inference('sup-', [status(thm)], ['228', '229'])).
% 1.26/1.42  thf('231', plain, (~ (v2_struct_0 @ sk_B)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('232', plain, (((v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 1.26/1.42      inference('clc', [status(thm)], ['230', '231'])).
% 1.26/1.42  thf('233', plain, (~ (v2_struct_0 @ sk_C)),
% 1.26/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.42  thf('234', plain, ((v2_struct_0 @ sk_A)),
% 1.26/1.42      inference('clc', [status(thm)], ['232', '233'])).
% 1.26/1.42  thf('235', plain, ($false), inference('demod', [status(thm)], ['0', '234'])).
% 1.26/1.42  
% 1.26/1.42  % SZS output end Refutation
% 1.26/1.42  
% 1.26/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
