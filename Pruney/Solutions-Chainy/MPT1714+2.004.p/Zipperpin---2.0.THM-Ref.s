%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IEEe60d784

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:18 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 818 expanded)
%              Number of leaves         :   25 ( 242 expanded)
%              Depth                    :   27
%              Number of atoms          : 1205 (11861 expanded)
%              Number of equality atoms :    8 (  30 expanded)
%              Maximal formula depth    :   16 (   6 average)

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

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf('2',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['18'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('21',plain,
    ( ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','34'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('37',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('43',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

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

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('52',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('53',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['13','58'])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('61',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('65',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('68',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('69',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('72',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('75',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('77',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['64','79'])).

thf('81',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('82',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['63','82'])).

thf('84',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['83','88'])).

thf('90',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ( r1_tsep_1 @ sk_B @ sk_D_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['62','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('92',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('97',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('98',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('99',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('100',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('101',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('104',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('109',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['98','108'])).

thf('110',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('111',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['97','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('114',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['96','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['86','87'])).

thf('117',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['93'])).

thf('119',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['93'])).

thf('121',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('122',plain,(
    r1_tsep_1 @ sk_D_1 @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['95','119','120','121'])).

thf('123',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 )
    | ~ ( l1_struct_0 @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['61','122'])).

thf('124',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','123'])).

thf('125',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['86','87'])).

thf('126',plain,
    ( ~ ( l1_struct_0 @ sk_D_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_1 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['93'])).

thf('128',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('129',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('130',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('131',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['130','133'])).

thf('135',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('136',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_1 )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ~ ( l1_pre_topc @ sk_D_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['129','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('139',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D_1 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['128','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['86','87'])).

thf('142',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( r1_tsep_1 @ sk_D_1 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_1 @ sk_B ) ),
    inference(split,[status(esa)],['93'])).

thf('144',plain,
    ( ( r1_tsep_1 @ sk_D_1 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['95','119','121','144','120'])).

thf('146',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['127','145'])).

thf('147',plain,(
    ~ ( l1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['126','146'])).

thf('148',plain,(
    ~ ( l1_pre_topc @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','147'])).

thf('149',plain,(
    l1_pre_topc @ sk_D_1 ),
    inference(demod,[status(thm)],['32','33'])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['148','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IEEe60d784
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 202 iterations in 0.104s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.38/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.56  thf(dt_l1_pre_topc, axiom,
% 0.38/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.56  thf('0', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('1', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf(t23_tmap_1, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.56               ( ![D:$i]:
% 0.38/0.56                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.56                   ( ( m1_pre_topc @ B @ C ) =>
% 0.38/0.56                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.38/0.56                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.38/0.56                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.56            ( l1_pre_topc @ A ) ) =>
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.56              ( ![C:$i]:
% 0.38/0.56                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.56                  ( ![D:$i]:
% 0.38/0.56                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.38/0.56                      ( ( m1_pre_topc @ B @ C ) =>
% 0.38/0.56                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.38/0.56                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.38/0.56                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.38/0.56  thf('2', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('3', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t4_tsep_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( m1_pre_topc @ C @ A ) =>
% 0.38/0.56               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.38/0.56                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X24 @ X25)
% 0.38/0.56          | ~ (m1_pre_topc @ X24 @ X26)
% 0.38/0.56          | (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 0.38/0.56          | ~ (m1_pre_topc @ X26 @ X25)
% 0.38/0.56          | ~ (l1_pre_topc @ X25)
% 0.38/0.56          | ~ (v2_pre_topc @ X25))),
% 0.38/0.56      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v2_pre_topc @ sk_A)
% 0.38/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.56          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.38/0.56          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.56  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.38/0.56          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.38/0.56          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      ((~ (m1_pre_topc @ sk_B @ sk_C_1)
% 0.38/0.56        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '8'])).
% 0.38/0.56  thf('10', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf(t28_xboole_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i]:
% 0.38/0.56         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.38/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (((k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56         = (u1_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (((r1_tsep_1 @ sk_C_1 @ sk_D_1) | (r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (((r1_tsep_1 @ sk_D_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('split', [status(esa)], ['18'])).
% 0.38/0.56  thf(symmetry_r1_tsep_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.38/0.56       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X22 : $i, X23 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X22)
% 0.38/0.56          | ~ (l1_struct_0 @ X23)
% 0.38/0.56          | (r1_tsep_1 @ X23 @ X22)
% 0.38/0.56          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.38/0.56      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      ((((r1_tsep_1 @ sk_C_1 @ sk_D_1)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_C_1)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_C_1)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_D_1)
% 0.38/0.56         | (r1_tsep_1 @ sk_C_1 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['17', '21'])).
% 0.38/0.56  thf('23', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(dt_m1_pre_topc, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X18 : $i, X19 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X18 @ X19)
% 0.38/0.56          | (l1_pre_topc @ X18)
% 0.38/0.56          | ~ (l1_pre_topc @ X19))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.56  thf('25', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('27', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_C_1 @ sk_D_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['22', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_C_1 @ sk_D_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['16', '28'])).
% 0.38/0.56  thf('30', plain, ((m1_pre_topc @ sk_D_1 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      (![X18 : $i, X19 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X18 @ X19)
% 0.38/0.56          | (l1_pre_topc @ X18)
% 0.38/0.56          | ~ (l1_pre_topc @ X19))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.56  thf('32', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.56  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('34', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (((r1_tsep_1 @ sk_C_1 @ sk_D_1)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['29', '34'])).
% 0.38/0.56  thf(d3_tsep_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_struct_0 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( l1_struct_0 @ B ) =>
% 0.38/0.56           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.38/0.56             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X20 : $i, X21 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X20)
% 0.38/0.56          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.38/0.56          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.38/0.56          | ~ (l1_struct_0 @ X21))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_C_1)
% 0.38/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))
% 0.38/0.56         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_C_1)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_D_1)
% 0.38/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '37'])).
% 0.38/0.56  thf('39', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_D_1)
% 0.38/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_D_1)
% 0.38/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['14', '40'])).
% 0.38/0.56  thf('42', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf(t3_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.38/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.38/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.38/0.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X8 @ X6)
% 0.38/0.56          | ~ (r2_hidden @ X8 @ X9)
% 0.38/0.56          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X1 @ X0)
% 0.38/0.56          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.38/0.56          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X0 @ X1)
% 0.38/0.56          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.38/0.56          | (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['44', '47'])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('simplify', [status(thm)], ['48'])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '49'])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.56  thf(d4_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.38/0.56  thf('52', plain,
% 0.38/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.38/0.56          | (r2_hidden @ X4 @ X2)
% 0.38/0.56          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.56         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['52'])).
% 0.38/0.56  thf('54', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.38/0.56          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['51', '53'])).
% 0.38/0.56  thf('55', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X1 @ X0)
% 0.38/0.56          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.38/0.56          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.38/0.56          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.38/0.56          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.56  thf('57', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r1_xboole_0 @ X2 @ X0)
% 0.38/0.56          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.38/0.56      inference('simplify', [status(thm)], ['56'])).
% 0.38/0.56  thf('58', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1)) @ 
% 0.38/0.56           (u1_struct_0 @ sk_D_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['50', '57'])).
% 0.38/0.56  thf('59', plain,
% 0.38/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['13', '58'])).
% 0.38/0.56  thf('60', plain,
% 0.38/0.56      (![X20 : $i, X21 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X20)
% 0.38/0.56          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.38/0.56          | (r1_tsep_1 @ X21 @ X20)
% 0.38/0.56          | ~ (l1_struct_0 @ X21))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.38/0.56  thf('61', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_B)
% 0.38/0.56         | (r1_tsep_1 @ sk_B @ sk_D_1)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('63', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('64', plain,
% 0.38/0.56      (((k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56         = (u1_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('65', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('66', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('67', plain,
% 0.38/0.56      (((r1_tsep_1 @ sk_C_1 @ sk_D_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('split', [status(esa)], ['18'])).
% 0.38/0.56  thf('68', plain,
% 0.38/0.56      (![X20 : $i, X21 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X20)
% 0.38/0.56          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.38/0.56          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.38/0.56          | ~ (l1_struct_0 @ X21))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.38/0.56  thf('69', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_C_1)
% 0.38/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))
% 0.38/0.56         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_C_1)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_D_1)
% 0.38/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['66', '69'])).
% 0.38/0.56  thf('71', plain, ((l1_pre_topc @ sk_C_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('72', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_D_1)
% 0.38/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['70', '71'])).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_D_1)
% 0.38/0.56         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1))))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['65', '72'])).
% 0.38/0.56  thf('74', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.56      inference('simplify', [status(thm)], ['48'])).
% 0.38/0.56  thf('77', plain,
% 0.38/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['75', '76'])).
% 0.38/0.56  thf('78', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r1_xboole_0 @ X2 @ X0)
% 0.38/0.56          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.38/0.56      inference('simplify', [status(thm)], ['56'])).
% 0.38/0.56  thf('79', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (r1_xboole_0 @ (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1)) @ 
% 0.38/0.56           (u1_struct_0 @ sk_D_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['77', '78'])).
% 0.38/0.56  thf('80', plain,
% 0.38/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['64', '79'])).
% 0.38/0.56  thf('81', plain,
% 0.38/0.56      (![X20 : $i, X21 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X20)
% 0.38/0.56          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.38/0.56          | (r1_tsep_1 @ X21 @ X20)
% 0.38/0.56          | ~ (l1_struct_0 @ X21))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.38/0.56  thf('82', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_B)
% 0.38/0.56         | (r1_tsep_1 @ sk_B @ sk_D_1)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['80', '81'])).
% 0.38/0.56  thf('83', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_B)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_D_1)
% 0.38/0.56         | (r1_tsep_1 @ sk_B @ sk_D_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['63', '82'])).
% 0.38/0.56  thf('84', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('85', plain,
% 0.38/0.56      (![X18 : $i, X19 : $i]:
% 0.38/0.56         (~ (m1_pre_topc @ X18 @ X19)
% 0.38/0.56          | (l1_pre_topc @ X18)
% 0.38/0.56          | ~ (l1_pre_topc @ X19))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.56  thf('86', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['84', '85'])).
% 0.38/0.56  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.56      inference('demod', [status(thm)], ['86', '87'])).
% 0.38/0.56  thf('89', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['83', '88'])).
% 0.38/0.56  thf('90', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['62', '89'])).
% 0.38/0.56  thf('91', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('92', plain,
% 0.38/0.56      (((r1_tsep_1 @ sk_B @ sk_D_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['90', '91'])).
% 0.38/0.56  thf('93', plain,
% 0.38/0.56      ((~ (r1_tsep_1 @ sk_B @ sk_D_1) | ~ (r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('94', plain,
% 0.38/0.56      ((~ (r1_tsep_1 @ sk_B @ sk_D_1)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_1)))),
% 0.38/0.56      inference('split', [status(esa)], ['93'])).
% 0.38/0.56  thf('95', plain,
% 0.38/0.56      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_1)) | ((r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['92', '94'])).
% 0.38/0.56  thf('96', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('97', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('98', plain,
% 0.38/0.56      (((k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56         = (u1_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('99', plain,
% 0.38/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['75', '76'])).
% 0.38/0.56  thf('100', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.56  thf('101', plain,
% 0.38/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.38/0.56         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['52'])).
% 0.38/0.56  thf('102', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.56          | (r2_hidden @ (sk_C @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['100', '101'])).
% 0.38/0.56  thf('103', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.56  thf('104', plain,
% 0.38/0.56      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X8 @ X6)
% 0.38/0.56          | ~ (r2_hidden @ X8 @ X9)
% 0.38/0.56          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.38/0.56  thf('105', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X0 @ X1)
% 0.38/0.56          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.38/0.56          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['103', '104'])).
% 0.38/0.56  thf('106', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         ((r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))
% 0.38/0.56          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.38/0.56          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['102', '105'])).
% 0.38/0.56  thf('107', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r1_xboole_0 @ X1 @ X0)
% 0.38/0.56          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['106'])).
% 0.38/0.56  thf('108', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.56           (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['99', '107'])).
% 0.38/0.56  thf('109', plain,
% 0.38/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['98', '108'])).
% 0.38/0.56  thf('110', plain,
% 0.38/0.56      (![X20 : $i, X21 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X20)
% 0.38/0.56          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.38/0.56          | (r1_tsep_1 @ X21 @ X20)
% 0.38/0.56          | ~ (l1_struct_0 @ X21))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.38/0.56  thf('111', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_D_1)
% 0.38/0.56         | (r1_tsep_1 @ sk_D_1 @ sk_B)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['109', '110'])).
% 0.38/0.56  thf('112', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_D_1)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_B)
% 0.38/0.56         | (r1_tsep_1 @ sk_D_1 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['97', '111'])).
% 0.38/0.56  thf('113', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('114', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['112', '113'])).
% 0.38/0.56  thf('115', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['96', '114'])).
% 0.38/0.56  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.56      inference('demod', [status(thm)], ['86', '87'])).
% 0.38/0.56  thf('117', plain,
% 0.38/0.56      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['115', '116'])).
% 0.38/0.56  thf('118', plain,
% 0.38/0.56      ((~ (r1_tsep_1 @ sk_D_1 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_1 @ sk_B)))),
% 0.38/0.56      inference('split', [status(esa)], ['93'])).
% 0.38/0.56  thf('119', plain,
% 0.38/0.56      (((r1_tsep_1 @ sk_D_1 @ sk_B)) | ~ ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['117', '118'])).
% 0.38/0.56  thf('120', plain,
% 0.38/0.56      (~ ((r1_tsep_1 @ sk_B @ sk_D_1)) | ~ ((r1_tsep_1 @ sk_D_1 @ sk_B))),
% 0.38/0.56      inference('split', [status(esa)], ['93'])).
% 0.38/0.56  thf('121', plain,
% 0.38/0.56      (((r1_tsep_1 @ sk_D_1 @ sk_C_1)) | ((r1_tsep_1 @ sk_C_1 @ sk_D_1))),
% 0.38/0.56      inference('split', [status(esa)], ['18'])).
% 0.38/0.56  thf('122', plain, (((r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['95', '119', '120', '121'])).
% 0.38/0.56  thf('123', plain,
% 0.38/0.56      ((~ (l1_struct_0 @ sk_B)
% 0.38/0.56        | (r1_tsep_1 @ sk_B @ sk_D_1)
% 0.38/0.56        | ~ (l1_struct_0 @ sk_D_1))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['61', '122'])).
% 0.38/0.56  thf('124', plain,
% 0.38/0.56      ((~ (l1_pre_topc @ sk_B)
% 0.38/0.56        | ~ (l1_struct_0 @ sk_D_1)
% 0.38/0.56        | (r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '123'])).
% 0.38/0.56  thf('125', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.56      inference('demod', [status(thm)], ['86', '87'])).
% 0.38/0.56  thf('126', plain, ((~ (l1_struct_0 @ sk_D_1) | (r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['124', '125'])).
% 0.38/0.56  thf('127', plain,
% 0.38/0.56      ((~ (r1_tsep_1 @ sk_B @ sk_D_1)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_1)))),
% 0.38/0.56      inference('split', [status(esa)], ['93'])).
% 0.38/0.56  thf('128', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('129', plain,
% 0.38/0.56      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.56  thf('130', plain,
% 0.38/0.56      (((k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.38/0.56         = (u1_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.56  thf('131', plain,
% 0.38/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_C_1)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '49'])).
% 0.38/0.56  thf('132', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r1_xboole_0 @ X1 @ X0)
% 0.38/0.56          | (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['106'])).
% 0.38/0.56  thf('133', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ 
% 0.38/0.56           (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_C_1))))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['131', '132'])).
% 0.38/0.56  thf('134', plain,
% 0.38/0.56      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_1) @ (u1_struct_0 @ sk_B)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['130', '133'])).
% 0.38/0.56  thf('135', plain,
% 0.38/0.56      (![X20 : $i, X21 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X20)
% 0.38/0.56          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.38/0.56          | (r1_tsep_1 @ X21 @ X20)
% 0.38/0.56          | ~ (l1_struct_0 @ X21))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.38/0.56  thf('136', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_D_1)
% 0.38/0.56         | (r1_tsep_1 @ sk_D_1 @ sk_B)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['134', '135'])).
% 0.38/0.56  thf('137', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_D_1)
% 0.38/0.56         | ~ (l1_struct_0 @ sk_B)
% 0.38/0.56         | (r1_tsep_1 @ sk_D_1 @ sk_B))) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['129', '136'])).
% 0.38/0.56  thf('138', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('139', plain,
% 0.38/0.56      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['137', '138'])).
% 0.38/0.56  thf('140', plain,
% 0.38/0.56      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D_1 @ sk_B)))
% 0.38/0.56         <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['128', '139'])).
% 0.38/0.56  thf('141', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.56      inference('demod', [status(thm)], ['86', '87'])).
% 0.38/0.56  thf('142', plain,
% 0.38/0.56      (((r1_tsep_1 @ sk_D_1 @ sk_B)) <= (((r1_tsep_1 @ sk_D_1 @ sk_C_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['140', '141'])).
% 0.38/0.56  thf('143', plain,
% 0.38/0.56      ((~ (r1_tsep_1 @ sk_D_1 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_1 @ sk_B)))),
% 0.38/0.56      inference('split', [status(esa)], ['93'])).
% 0.38/0.56  thf('144', plain,
% 0.38/0.56      (((r1_tsep_1 @ sk_D_1 @ sk_B)) | ~ ((r1_tsep_1 @ sk_D_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['142', '143'])).
% 0.38/0.56  thf('145', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D_1))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)],
% 0.38/0.56                ['95', '119', '121', '144', '120'])).
% 0.38/0.56  thf('146', plain, (~ (r1_tsep_1 @ sk_B @ sk_D_1)),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['127', '145'])).
% 0.38/0.56  thf('147', plain, (~ (l1_struct_0 @ sk_D_1)),
% 0.38/0.56      inference('clc', [status(thm)], ['126', '146'])).
% 0.38/0.56  thf('148', plain, (~ (l1_pre_topc @ sk_D_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['0', '147'])).
% 0.38/0.56  thf('149', plain, ((l1_pre_topc @ sk_D_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('150', plain, ($false), inference('demod', [status(thm)], ['148', '149'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
