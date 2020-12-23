%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.36cPjnhKyL

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 761 expanded)
%              Number of leaves         :   23 ( 225 expanded)
%              Depth                    :   29
%              Number of atoms          :  893 (11051 expanded)
%              Number of equality atoms :   10 (  42 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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

thf('6',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_tsep_1 @ X15 @ X14 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('9',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      = ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X20 )
      | ( r1_tarski @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_xboole_0 @ X6 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['25','37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('40',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['3','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['2','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('50',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('52',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('59',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_tsep_1 @ X15 @ X14 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('61',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('64',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('67',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('69',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      = ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_xboole_0 @ X6 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      = ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('78',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('80',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['56','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('83',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['55','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('86',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('88',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['54','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('91',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['53','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('94',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('99',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['95'])).

thf('100',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['95'])).

thf('102',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('103',plain,(
    r1_tsep_1 @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['97','100','101','102'])).

thf('104',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( l1_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['52','103'])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['1','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('107',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['95'])).

thf('109',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('110',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['95'])).

thf('111',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['97','100','102','111','101'])).

thf('113',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['108','112'])).

thf('114',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['107','113'])).

thf('115',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['115','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.36cPjnhKyL
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:21:42 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 126 iterations in 0.041s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('0', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('1', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('2', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('3', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('4', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('5', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf(t24_tmap_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.51                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.51                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.51                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.21/0.51                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
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
% 0.21/0.51                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.51                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.21/0.51                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.21/0.51  thf('6', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['6'])).
% 0.21/0.51  thf(d3_tsep_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( l1_struct_0 @ B ) =>
% 0.21/0.51           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.51             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X14)
% 0.21/0.51          | ~ (r1_tsep_1 @ X15 @ X14)
% 0.21/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.21/0.51          | ~ (l1_struct_0 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.21/0.51         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '9'])).
% 0.21/0.51  thf('11', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.21/0.51          | (l1_pre_topc @ X12)
% 0.21/0.51          | ~ (l1_pre_topc @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('13', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '16'])).
% 0.21/0.51  thf('18', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.21/0.51          | (l1_pre_topc @ X12)
% 0.21/0.51          | ~ (l1_pre_topc @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('20', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '22'])).
% 0.21/0.51  thf(t83_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      ((((k4_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.21/0.51          = (u1_struct_0 @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
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
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.51          | ~ (m1_pre_topc @ X18 @ X20)
% 0.21/0.51          | (r1_tarski @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (m1_pre_topc @ X20 @ X19)
% 0.21/0.51          | ~ (l1_pre_topc @ X19)
% 0.21/0.51          | ~ (v2_pre_topc @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v2_pre_topc @ sk_A)
% 0.21/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.51          | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (m1_pre_topc @ sk_B @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((~ (m1_pre_topc @ sk_B @ sk_C)
% 0.21/0.51        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '32'])).
% 0.21/0.51  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('35', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf(t85_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X6 @ X7)
% 0.21/0.51          | (r1_xboole_0 @ X6 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51          (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['25', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X14)
% 0.21/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.21/0.51          | (r1_tsep_1 @ X15 @ X14)
% 0.21/0.51          | ~ (l1_struct_0 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '40'])).
% 0.21/0.51  thf('42', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.21/0.51          | (l1_pre_topc @ X12)
% 0.21/0.51          | ~ (l1_pre_topc @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('44', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('46', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['41', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '47'])).
% 0.21/0.51  thf('49', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.51       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X16)
% 0.21/0.51          | ~ (l1_struct_0 @ X17)
% 0.21/0.51          | (r1_tsep_1 @ X17 @ X16)
% 0.21/0.51          | ~ (r1_tsep_1 @ X16 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['6'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X14)
% 0.21/0.51          | ~ (r1_tsep_1 @ X15 @ X14)
% 0.21/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.21/0.51          | ~ (l1_struct_0 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '61'])).
% 0.21/0.51  thf('63', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('64', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '64'])).
% 0.21/0.51  thf('66', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      ((((k4_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.21/0.51          = (u1_struct_0 @ sk_C)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('71', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X6 @ X7)
% 0.21/0.51          | (r1_xboole_0 @ X6 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (((k4_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      ((((k4_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.21/0.51          = (u1_struct_0 @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['69', '75'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51          (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['76', '77'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X14)
% 0.21/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.21/0.51          | (r1_tsep_1 @ X15 @ X14)
% 0.21/0.51          | ~ (l1_struct_0 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['56', '80'])).
% 0.21/0.51  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['55', '83'])).
% 0.21/0.51  thf('85', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf('87', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X16)
% 0.21/0.51          | ~ (l1_struct_0 @ X17)
% 0.21/0.51          | (r1_tsep_1 @ X17 @ X16)
% 0.21/0.51          | ~ (r1_tsep_1 @ X16 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '88'])).
% 0.21/0.51  thf('90', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '91'])).
% 0.21/0.51  thf('93', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('94', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['92', '93'])).
% 0.21/0.51  thf('95', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('96', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['95'])).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['94', '96'])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['95'])).
% 0.21/0.51  thf('100', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.51  thf('101', plain,
% 0.21/0.51      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.51      inference('split', [status(esa)], ['95'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_C @ sk_D))),
% 0.21/0.51      inference('split', [status(esa)], ['6'])).
% 0.21/0.51  thf('103', plain, (((r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['97', '100', '101', '102'])).
% 0.21/0.51  thf('104', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_D)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['52', '103'])).
% 0.21/0.51  thf('105', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_D)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.51        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '104'])).
% 0.21/0.51  thf('106', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('107', plain, ((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['105', '106'])).
% 0.21/0.51  thf('108', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['95'])).
% 0.21/0.51  thf('109', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['95'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['109', '110'])).
% 0.21/0.51  thf('112', plain, (~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)],
% 0.21/0.51                ['97', '100', '102', '111', '101'])).
% 0.21/0.51  thf('113', plain, (~ (r1_tsep_1 @ sk_D @ sk_B)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['108', '112'])).
% 0.21/0.51  thf('114', plain, (~ (l1_struct_0 @ sk_B)),
% 0.21/0.51      inference('clc', [status(thm)], ['107', '113'])).
% 0.21/0.51  thf('115', plain, (~ (l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '114'])).
% 0.21/0.51  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('117', plain, ($false), inference('demod', [status(thm)], ['115', '116'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
