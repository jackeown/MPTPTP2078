%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m69W5EPtX6

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 875 expanded)
%              Number of leaves         :   25 ( 258 expanded)
%              Depth                    :   29
%              Number of atoms          : 1070 (12558 expanded)
%              Number of equality atoms :    5 (  30 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('9',plain,
    ( ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('25',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('28',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('31',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

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

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('61',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('63',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('66',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('70',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('71',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('72',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('73',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('76',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('79',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('81',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('83',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('85',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('87',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['68','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('90',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['67','90'])).

thf('92',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('98',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['98'])).

thf('100',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('101',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('102',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','58'])).

thf('103',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('104',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['94','95'])).

thf('107',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('110',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['98'])).

thf('112',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('114',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('115',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('116',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('117',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['94','95'])).

thf('120',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['113','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('123',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['98'])).

thf('125',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('127',plain,
    ( ~ ( r1_tsep_1 @ sk_D_1 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['98'])).

thf('128',plain,(
    ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['112','125','126','127'])).

thf('129',plain,(
    ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['99','128'])).

thf('130',plain,(
    ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['97','129'])).

thf('131',plain,(
    r1_tsep_1 @ sk_D_1 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['130','126'])).

thf('132',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['66','131'])).

thf('133',plain,(
    ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['99','128'])).

thf('134',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['94','95'])).

thf('137',plain,(
    $false ),
    inference(demod,[status(thm)],['135','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m69W5EPtX6
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 135 iterations in 0.056s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('0', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('1', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('2', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('3', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('4', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('5', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf(t23_tmap_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.51                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.51                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.21/0.51                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.51                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51                  ( ![D:$i]:
% 0.21/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.51                      ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.51                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.21/0.51                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.51                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_C_1 @ sk_D_1) | (r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('split', [status(esa)], ['6'])).
% 0.21/0.51  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.51       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X22 : $i, X23 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X22)
% 0.21/0.51          | ~ (l1_struct_0 @ X23)
% 0.21/0.51          | (r1_tsep_1 @ X23 @ X22)
% 0.21/0.51          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((((r1_tsep_1 @ sk_C_1 @ sk_D_1)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D_1)
% 0.21/0.51         | (r1_tsep_1 @ sk_C_1 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '9'])).
% 0.21/0.51  thf('11', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.51          | (l1_pre_topc @ X18)
% 0.21/0.51          | ~ (l1_pre_topc @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_C_1 @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_C_1 @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '16'])).
% 0.21/0.51  thf('18', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.51          | (l1_pre_topc @ X18)
% 0.21/0.51          | ~ (l1_pre_topc @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_C_1 @ sk_D_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '22'])).
% 0.21/0.51  thf(d3_tsep_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( l1_struct_0 @ B ) =>
% 0.21/0.51           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.51             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X20)
% 0.21/0.51          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.21/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (l1_struct_0 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D_1)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '25'])).
% 0.21/0.51  thf('27', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D_1)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D_1)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '28'])).
% 0.21/0.51  thf('30', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf(t3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.51          | ~ (r2_hidden @ X8 @ X9)
% 0.21/0.51          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.51          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.51          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.51          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '37'])).
% 0.21/0.51  thf('39', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t4_tsep_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.51               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.21/0.51                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X24 @ X25)
% 0.21/0.51          | ~ (m1_pre_topc @ X24 @ X26)
% 0.21/0.51          | (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 0.21/0.51          | ~ (m1_pre_topc @ X26 @ X25)
% 0.21/0.51          | ~ (l1_pre_topc @ X25)
% 0.21/0.51          | ~ (v2_pre_topc @ X25))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((~ (m1_pre_topc @ sk_B @ sk_C_1)
% 0.21/0.51        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '45'])).
% 0.21/0.51  thf('47', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.51  thf(t12_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]:
% 0.21/0.51         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.51         = (u1_struct_0 @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.51  thf(d3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.51           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X3)
% 0.21/0.51          | (r2_hidden @ X0 @ X2)
% 0.21/0.51          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.21/0.51      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.51          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '53'])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.51          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X1 @ X2)
% 0.21/0.51          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.21/0.51          | (r1_xboole_0 @ X1 @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.21/0.51          | (r1_xboole_0 @ X1 @ X2))),
% 0.21/0.51      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.51          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '57'])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X20)
% 0.21/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.51          | (r1_tsep_1 @ X21 @ X20)
% 0.21/0.51          | ~ (l1_struct_0 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D_1)
% 0.21/0.51         | (r1_tsep_1 @ sk_D_1 @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D_1)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tsep_1 @ sk_D_1 @ sk_B))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '63'])).
% 0.21/0.51  thf('65', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_C_1 @ sk_D_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('split', [status(esa)], ['6'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X20)
% 0.21/0.51          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.21/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (l1_struct_0 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D_1)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['70', '73'])).
% 0.21/0.51  thf('75', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D_1)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D_1)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['69', '76'])).
% 0.21/0.51  thf('78', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.51  thf('82', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.21/0.51          | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '57'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.51  thf('85', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X20)
% 0.21/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.51          | (r1_tsep_1 @ X21 @ X20)
% 0.21/0.51          | ~ (l1_struct_0 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D_1)
% 0.21/0.51         | (r1_tsep_1 @ sk_D_1 @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D_1)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tsep_1 @ sk_D_1 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['68', '87'])).
% 0.21/0.51  thf('89', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('90', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['88', '89'])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '90'])).
% 0.21/0.51  thf('92', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('93', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.51          | (l1_pre_topc @ X18)
% 0.21/0.51          | ~ (l1_pre_topc @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('94', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.51  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('96', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['91', '96'])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D_1) | ~ (r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_D_1 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_1 @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['98'])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('101', plain,
% 0.21/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '58'])).
% 0.21/0.51  thf('103', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X20)
% 0.21/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.51          | (r1_tsep_1 @ X21 @ X20)
% 0.21/0.51          | ~ (l1_struct_0 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('104', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tsep_1 @ sk_B @ sk_D_1)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.51  thf('105', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D_1)
% 0.21/0.51         | (r1_tsep_1 @ sk_B @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['101', '104'])).
% 0.21/0.51  thf('106', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.51  thf('107', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['105', '106'])).
% 0.21/0.51  thf('108', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['100', '107'])).
% 0.21/0.51  thf('109', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['108', '109'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D_1)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_1)))),
% 0.21/0.51      inference('split', [status(esa)], ['98'])).
% 0.21/0.51  thf('112', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D_1)) | ~ ((r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['110', '111'])).
% 0.21/0.51  thf('113', plain,
% 0.21/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('114', plain,
% 0.21/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('115', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.51  thf('116', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X20)
% 0.21/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.51          | (r1_tsep_1 @ X21 @ X20)
% 0.21/0.51          | ~ (l1_struct_0 @ X21))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('117', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tsep_1 @ sk_B @ sk_D_1)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['115', '116'])).
% 0.21/0.51  thf('118', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D_1)
% 0.21/0.51         | (r1_tsep_1 @ sk_B @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['114', '117'])).
% 0.21/0.51  thf('119', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.51  thf('120', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['118', '119'])).
% 0.21/0.51  thf('121', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['113', '120'])).
% 0.21/0.51  thf('122', plain, ((l1_pre_topc @ sk_D_1)),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('123', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['121', '122'])).
% 0.21/0.51  thf('124', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D_1)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_1)))),
% 0.21/0.51      inference('split', [status(esa)], ['98'])).
% 0.21/0.51  thf('125', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D_1)) | ~ ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['123', '124'])).
% 0.21/0.51  thf('126', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D_1 @ sk_C_1)) | ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.21/0.51      inference('split', [status(esa)], ['6'])).
% 0.21/0.51  thf('127', plain,
% 0.21/0.51      (~ ((r1_tsep_1 @ sk_D_1 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.21/0.51      inference('split', [status(esa)], ['98'])).
% 0.21/0.51  thf('128', plain, (~ ((r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['112', '125', '126', '127'])).
% 0.21/0.51  thf('129', plain, (~ (r1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['99', '128'])).
% 0.21/0.51  thf('130', plain, (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['97', '129'])).
% 0.21/0.51  thf('131', plain, (((r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['130', '126'])).
% 0.21/0.51  thf('132', plain, ((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['66', '131'])).
% 0.21/0.51  thf('133', plain, (~ (r1_tsep_1 @ sk_D_1 @ sk_B)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['99', '128'])).
% 0.21/0.51  thf('134', plain, (~ (l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('clc', [status(thm)], ['132', '133'])).
% 0.21/0.51  thf('135', plain, (~ (l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '134'])).
% 0.21/0.51  thf('136', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.51  thf('137', plain, ($false), inference('demod', [status(thm)], ['135', '136'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
