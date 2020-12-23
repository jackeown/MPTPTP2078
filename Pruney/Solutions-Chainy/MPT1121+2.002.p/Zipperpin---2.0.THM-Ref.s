%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1RE8nKkWY4

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 244 expanded)
%              Number of leaves         :   24 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          : 1254 (3761 expanded)
%              Number of equality atoms :   29 ( 206 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t52_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v4_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ B )
                  = B ) )
              & ( ( ( v2_pre_topc @ A )
                  & ( ( k2_pre_topc @ A @ B )
                    = B ) )
               => ( v4_pre_topc @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_pre_topc])).

thf('0',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ( v2_pre_topc @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v2_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r1_tarski @ X8 @ X6 )
      | ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( v4_pre_topc @ D @ A )
                        & ( r1_tarski @ B @ D ) )
                     => ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X15 @ ( k2_pre_topc @ X14 @ X13 ) )
      | ~ ( v4_pre_topc @ X16 @ X14 )
      | ~ ( r1_tarski @ X13 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r2_hidden @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( r1_tarski @ sk_B @ sk_B )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ sk_B @ sk_A )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ( r2_hidden @ X0 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( r1_tarski @ X8 @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X6 @ X8 @ X7 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('35',plain,
    ( ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ X20 @ ( k2_pre_topc @ X21 @ X20 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(split,[status(esa)],['45'])).

thf('47',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
       != sk_B )
      & ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(split,[status(esa)],['45'])).

thf('50',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ? [C: $i] :
              ( ( ( k2_pre_topc @ A @ B )
                = ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ C ) )
              & ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ D @ C )
                  <=> ( ( v4_pre_topc @ D @ A )
                      & ( r1_tarski @ B @ D ) ) ) )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('54',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf(t44_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) )
           => ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('59',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ X19 @ X18 )
      | ~ ( r2_hidden @ X19 @ ( sk_C_1 @ X17 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
      | ~ ( r2_hidden @ ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('72',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('73',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( r2_hidden @ ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( ( v4_pre_topc @ ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['70','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ ( sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('79',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X12 ) @ X11 ) @ X12 )
      | ~ ( v4_pre_topc @ ( sk_C @ X11 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('80',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ~ ( v4_pre_topc @ ( sk_C @ ( sk_C_1 @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['77','83'])).

thf('85',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( k6_setfam_1 @ ( u1_struct_0 @ X18 ) @ ( sk_C_1 @ X17 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('88',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['84','91'])).

thf('93',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','92'])).

thf('94',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['45'])).

thf('95',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','48','49','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1RE8nKkWY4
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.60  % Solved by: fo/fo7.sh
% 0.20/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.60  % done 283 iterations in 0.145s
% 0.20/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.60  % SZS output start Refutation
% 0.20/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.60  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.60  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.60  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.60  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.60  thf(t52_pre_topc, conjecture,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( l1_pre_topc @ A ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.60             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.60               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.60    (~( ![A:$i]:
% 0.20/0.60        ( ( l1_pre_topc @ A ) =>
% 0.20/0.60          ( ![B:$i]:
% 0.20/0.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60              ( ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.60                  ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.60                ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.60                  ( v4_pre_topc @ B @ A ) ) ) ) ) ) )),
% 0.20/0.60    inference('cnf.neg', [status(esa)], [t52_pre_topc])).
% 0.20/0.60  thf('0', plain,
% 0.20/0.60      ((((k2_pre_topc @ sk_A @ sk_B) != (sk_B)) | (v2_pre_topc @ sk_A))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('1', plain,
% 0.20/0.60      (((v2_pre_topc @ sk_A)) | ~ (((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.20/0.60      inference('split', [status(esa)], ['0'])).
% 0.20/0.60  thf('2', plain,
% 0.20/0.60      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('3', plain,
% 0.20/0.60      (((v4_pre_topc @ sk_B @ sk_A)) | (((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.20/0.60      inference('split', [status(esa)], ['2'])).
% 0.20/0.60  thf('4', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(dt_k2_pre_topc, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.60       ( m1_subset_1 @
% 0.20/0.60         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.60  thf('5', plain,
% 0.20/0.60      (![X9 : $i, X10 : $i]:
% 0.20/0.60         (~ (l1_pre_topc @ X9)
% 0.20/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.60          | (m1_subset_1 @ (k2_pre_topc @ X9 @ X10) @ 
% 0.20/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X9))))),
% 0.20/0.60      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.20/0.60  thf('6', plain,
% 0.20/0.60      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.60  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('8', plain,
% 0.20/0.60      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.60  thf('9', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(t7_subset_1, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.60       ( ![C:$i]:
% 0.20/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.60           ( ( ![D:$i]:
% 0.20/0.60               ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.60                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.60             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.60  thf('10', plain,
% 0.20/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.60          | (r1_tarski @ X8 @ X6)
% 0.20/0.60          | (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X8)
% 0.20/0.60          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.60      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.60  thf('11', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60          | (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.60          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.60  thf('12', plain,
% 0.20/0.60      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.20/0.60        | (r2_hidden @ 
% 0.20/0.60           (sk_D @ sk_B @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60           (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.60  thf('13', plain,
% 0.20/0.60      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.60      inference('split', [status(esa)], ['2'])).
% 0.20/0.60  thf('14', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('15', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(t45_pre_topc, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( l1_pre_topc @ A ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60           ( ![C:$i]:
% 0.20/0.60             ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.60               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.60                 ( ![D:$i]:
% 0.20/0.60                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60                     ( ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) =>
% 0.20/0.60                       ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.60  thf('16', plain,
% 0.20/0.60      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.60          | ~ (r2_hidden @ X15 @ (k2_pre_topc @ X14 @ X13))
% 0.20/0.60          | ~ (v4_pre_topc @ X16 @ X14)
% 0.20/0.60          | ~ (r1_tarski @ X13 @ X16)
% 0.20/0.60          | (r2_hidden @ X15 @ X16)
% 0.20/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.60          | ~ (r2_hidden @ X15 @ (u1_struct_0 @ X14))
% 0.20/0.60          | ~ (l1_pre_topc @ X14))),
% 0.20/0.60      inference('cnf', [status(esa)], [t45_pre_topc])).
% 0.20/0.60  thf('17', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         (~ (l1_pre_topc @ sk_A)
% 0.20/0.60          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60          | (r2_hidden @ X0 @ X1)
% 0.20/0.60          | ~ (r1_tarski @ sk_B @ X1)
% 0.20/0.60          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.20/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.60  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('19', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]:
% 0.20/0.60         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60          | (r2_hidden @ X0 @ X1)
% 0.20/0.60          | ~ (r1_tarski @ sk_B @ X1)
% 0.20/0.60          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.20/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.60      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.60  thf('20', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.60          | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.60          | ~ (r1_tarski @ sk_B @ sk_B)
% 0.20/0.60          | (r2_hidden @ X0 @ sk_B)
% 0.20/0.60          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['14', '19'])).
% 0.20/0.60  thf(d10_xboole_0, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.60  thf('21', plain,
% 0.20/0.60      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.60  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.60  thf('23', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.60          | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.60          | (r2_hidden @ X0 @ sk_B)
% 0.20/0.60          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['20', '22'])).
% 0.20/0.60  thf('24', plain,
% 0.20/0.60      ((![X0 : $i]:
% 0.20/0.60          (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60           | (r2_hidden @ X0 @ sk_B)
% 0.20/0.60           | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.20/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['13', '23'])).
% 0.20/0.60  thf('25', plain,
% 0.20/0.60      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.60  thf(l3_subset_1, axiom,
% 0.20/0.60    (![A:$i,B:$i]:
% 0.20/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.60  thf('26', plain,
% 0.20/0.60      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.60         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.60          | (r2_hidden @ X3 @ X5)
% 0.20/0.60          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.20/0.60      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.60  thf('27', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.60          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.60  thf('28', plain,
% 0.20/0.60      ((![X0 : $i]:
% 0.20/0.60          (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.60           | (r2_hidden @ X0 @ sk_B)))
% 0.20/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.60      inference('clc', [status(thm)], ['24', '27'])).
% 0.20/0.60  thf('29', plain,
% 0.20/0.60      ((((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.20/0.60         | (r2_hidden @ 
% 0.20/0.60            (sk_D @ sk_B @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.60            sk_B)))
% 0.20/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['12', '28'])).
% 0.20/0.60  thf('30', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('31', plain,
% 0.20/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.60          | (r1_tarski @ X8 @ X6)
% 0.20/0.60          | ~ (r2_hidden @ (sk_D @ X6 @ X8 @ X7) @ X6)
% 0.20/0.60          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.60      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.60  thf('32', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.20/0.60          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.60  thf('33', plain,
% 0.20/0.60      ((((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.20/0.60         | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.20/0.60         | ~ (m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.60              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['29', '32'])).
% 0.20/0.60  thf('34', plain,
% 0.20/0.60      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.20/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.60  thf('35', plain,
% 0.20/0.60      ((((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.20/0.60         | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.20/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.60  thf('36', plain,
% 0.20/0.60      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.20/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.60      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.60  thf('37', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(t48_pre_topc, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( l1_pre_topc @ A ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.20/0.60  thf('38', plain,
% 0.20/0.60      (![X20 : $i, X21 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.60          | (r1_tarski @ X20 @ (k2_pre_topc @ X21 @ X20))
% 0.20/0.60          | ~ (l1_pre_topc @ X21))),
% 0.20/0.60      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.20/0.60  thf('39', plain,
% 0.20/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.60        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.60  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('41', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.20/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.60  thf('42', plain,
% 0.20/0.60      (![X0 : $i, X2 : $i]:
% 0.20/0.60         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.60  thf('43', plain,
% 0.20/0.60      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.20/0.60        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.60  thf('44', plain,
% 0.20/0.60      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.60         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['36', '43'])).
% 0.20/0.60  thf('45', plain,
% 0.20/0.60      ((((k2_pre_topc @ sk_A @ sk_B) != (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('46', plain,
% 0.20/0.60      ((((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))
% 0.20/0.60         <= (~ (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))))),
% 0.20/0.60      inference('split', [status(esa)], ['45'])).
% 0.20/0.60  thf('47', plain,
% 0.20/0.60      ((((sk_B) != (sk_B)))
% 0.20/0.60         <= (~ (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & 
% 0.20/0.60             ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['44', '46'])).
% 0.20/0.60  thf('48', plain,
% 0.20/0.60      (~ ((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.20/0.60       (((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.20/0.60      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.60  thf('49', plain,
% 0.20/0.60      (~ ((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.20/0.60       ~ (((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.20/0.60      inference('split', [status(esa)], ['45'])).
% 0.20/0.60  thf('50', plain,
% 0.20/0.60      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.20/0.60         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))))),
% 0.20/0.60      inference('split', [status(esa)], ['2'])).
% 0.20/0.60  thf('51', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('split', [status(esa)], ['0'])).
% 0.20/0.60  thf('52', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf(t46_pre_topc, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60           ( ?[C:$i]:
% 0.20/0.60             ( ( ( k2_pre_topc @ A @ B ) =
% 0.20/0.60                 ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) & 
% 0.20/0.60               ( ![D:$i]:
% 0.20/0.60                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60                   ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.60                     ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) ) ) ) & 
% 0.20/0.60               ( m1_subset_1 @
% 0.20/0.60                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.60  thf('53', plain,
% 0.20/0.60      (![X17 : $i, X18 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.60          | (m1_subset_1 @ (sk_C_1 @ X17 @ X18) @ 
% 0.20/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.20/0.60          | ~ (l1_pre_topc @ X18)
% 0.20/0.60          | ~ (v2_pre_topc @ X18))),
% 0.20/0.60      inference('cnf', [status(esa)], [t46_pre_topc])).
% 0.20/0.60  thf('54', plain,
% 0.20/0.60      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.60        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.20/0.60           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.60  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('56', plain,
% 0.20/0.60      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.60        | (m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.20/0.60           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.60      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.60  thf('57', plain,
% 0.20/0.60      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.20/0.60         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['51', '56'])).
% 0.20/0.60  thf(t44_pre_topc, axiom,
% 0.20/0.60    (![A:$i]:
% 0.20/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.60       ( ![B:$i]:
% 0.20/0.60         ( ( m1_subset_1 @
% 0.20/0.60             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.60           ( ( ![C:$i]:
% 0.20/0.60               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.60                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) =>
% 0.20/0.60             ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.60  thf('58', plain,
% 0.20/0.60      (![X11 : $i, X12 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X11 @ 
% 0.20/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.20/0.60          | (v4_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X12) @ X11) @ X12)
% 0.20/0.60          | (m1_subset_1 @ (sk_C @ X11 @ X12) @ 
% 0.20/0.60             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.60          | ~ (l1_pre_topc @ X12)
% 0.20/0.60          | ~ (v2_pre_topc @ X12))),
% 0.20/0.60      inference('cnf', [status(esa)], [t44_pre_topc])).
% 0.20/0.60  thf('59', plain,
% 0.20/0.60      (((~ (v2_pre_topc @ sk_A)
% 0.20/0.60         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.60         | (m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.60            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60         | (v4_pre_topc @ 
% 0.20/0.60            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.60            sk_A)))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.60  thf('60', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('split', [status(esa)], ['0'])).
% 0.20/0.60  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('62', plain,
% 0.20/0.60      ((((m1_subset_1 @ (sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.60          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60         | (v4_pre_topc @ 
% 0.20/0.60            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.60            sk_A)))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.60  thf('63', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('split', [status(esa)], ['0'])).
% 0.20/0.60  thf('64', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('65', plain,
% 0.20/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.60          | (v4_pre_topc @ X19 @ X18)
% 0.20/0.60          | ~ (r2_hidden @ X19 @ (sk_C_1 @ X17 @ X18))
% 0.20/0.60          | ~ (l1_pre_topc @ X18)
% 0.20/0.60          | ~ (v2_pre_topc @ X18))),
% 0.20/0.60      inference('cnf', [status(esa)], [t46_pre_topc])).
% 0.20/0.60  thf('66', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (v2_pre_topc @ sk_A)
% 0.20/0.60          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.60          | ~ (r2_hidden @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.20/0.60          | (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.60  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('68', plain,
% 0.20/0.60      (![X0 : $i]:
% 0.20/0.60         (~ (v2_pre_topc @ sk_A)
% 0.20/0.60          | ~ (r2_hidden @ X0 @ (sk_C_1 @ sk_B @ sk_A))
% 0.20/0.60          | (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.60      inference('demod', [status(thm)], ['66', '67'])).
% 0.20/0.60  thf('69', plain,
% 0.20/0.60      ((![X0 : $i]:
% 0.20/0.60          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.60           | (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.60           | ~ (r2_hidden @ X0 @ (sk_C_1 @ sk_B @ sk_A))))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['63', '68'])).
% 0.20/0.60  thf('70', plain,
% 0.20/0.60      ((((v4_pre_topc @ 
% 0.20/0.60          (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A)
% 0.20/0.60         | ~ (r2_hidden @ (sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.60              (sk_C_1 @ sk_B @ sk_A))
% 0.20/0.60         | (v4_pre_topc @ (sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) @ sk_A)))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['62', '69'])).
% 0.20/0.60  thf('71', plain,
% 0.20/0.60      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.20/0.60         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['51', '56'])).
% 0.20/0.60  thf('72', plain,
% 0.20/0.60      (![X11 : $i, X12 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X11 @ 
% 0.20/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.20/0.60          | (v4_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X12) @ X11) @ X12)
% 0.20/0.60          | (r2_hidden @ (sk_C @ X11 @ X12) @ X11)
% 0.20/0.60          | ~ (l1_pre_topc @ X12)
% 0.20/0.60          | ~ (v2_pre_topc @ X12))),
% 0.20/0.60      inference('cnf', [status(esa)], [t44_pre_topc])).
% 0.20/0.60  thf('73', plain,
% 0.20/0.60      (((~ (v2_pre_topc @ sk_A)
% 0.20/0.60         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.60         | (r2_hidden @ (sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.60            (sk_C_1 @ sk_B @ sk_A))
% 0.20/0.60         | (v4_pre_topc @ 
% 0.20/0.60            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.60            sk_A)))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.60  thf('74', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('split', [status(esa)], ['0'])).
% 0.20/0.60  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('76', plain,
% 0.20/0.60      ((((r2_hidden @ (sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) @ 
% 0.20/0.60          (sk_C_1 @ sk_B @ sk_A))
% 0.20/0.60         | (v4_pre_topc @ 
% 0.20/0.60            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.60            sk_A)))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.20/0.60  thf('77', plain,
% 0.20/0.60      ((((v4_pre_topc @ (sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.60         | (v4_pre_topc @ 
% 0.20/0.60            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.60            sk_A)))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('clc', [status(thm)], ['70', '76'])).
% 0.20/0.60  thf('78', plain,
% 0.20/0.60      (((m1_subset_1 @ (sk_C_1 @ sk_B @ sk_A) @ 
% 0.20/0.60         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['51', '56'])).
% 0.20/0.60  thf('79', plain,
% 0.20/0.60      (![X11 : $i, X12 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X11 @ 
% 0.20/0.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.20/0.60          | (v4_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X12) @ X11) @ X12)
% 0.20/0.60          | ~ (v4_pre_topc @ (sk_C @ X11 @ X12) @ X12)
% 0.20/0.60          | ~ (l1_pre_topc @ X12)
% 0.20/0.60          | ~ (v2_pre_topc @ X12))),
% 0.20/0.60      inference('cnf', [status(esa)], [t44_pre_topc])).
% 0.20/0.60  thf('80', plain,
% 0.20/0.60      (((~ (v2_pre_topc @ sk_A)
% 0.20/0.60         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.60         | ~ (v4_pre_topc @ (sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.60         | (v4_pre_topc @ 
% 0.20/0.60            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.60            sk_A)))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.60  thf('81', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('split', [status(esa)], ['0'])).
% 0.20/0.60  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('83', plain,
% 0.20/0.60      (((~ (v4_pre_topc @ (sk_C @ (sk_C_1 @ sk_B @ sk_A) @ sk_A) @ sk_A)
% 0.20/0.60         | (v4_pre_topc @ 
% 0.20/0.60            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ 
% 0.20/0.60            sk_A)))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.20/0.60  thf('84', plain,
% 0.20/0.60      (((v4_pre_topc @ 
% 0.20/0.60         (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A)) @ sk_A))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('clc', [status(thm)], ['77', '83'])).
% 0.20/0.60  thf('85', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('split', [status(esa)], ['0'])).
% 0.20/0.60  thf('86', plain,
% 0.20/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('87', plain,
% 0.20/0.60      (![X17 : $i, X18 : $i]:
% 0.20/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.60          | ((k2_pre_topc @ X18 @ X17)
% 0.20/0.60              = (k6_setfam_1 @ (u1_struct_0 @ X18) @ (sk_C_1 @ X17 @ X18)))
% 0.20/0.60          | ~ (l1_pre_topc @ X18)
% 0.20/0.60          | ~ (v2_pre_topc @ X18))),
% 0.20/0.60      inference('cnf', [status(esa)], [t46_pre_topc])).
% 0.20/0.60  thf('88', plain,
% 0.20/0.60      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.60        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.60            = (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.20/0.60      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.60  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.60  thf('90', plain,
% 0.20/0.60      ((~ (v2_pre_topc @ sk_A)
% 0.20/0.60        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.60            = (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A))))),
% 0.20/0.60      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.60  thf('91', plain,
% 0.20/0.60      ((((k2_pre_topc @ sk_A @ sk_B)
% 0.20/0.60          = (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_1 @ sk_B @ sk_A))))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('sup-', [status(thm)], ['85', '90'])).
% 0.20/0.60  thf('92', plain,
% 0.20/0.60      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))
% 0.20/0.60         <= (((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('demod', [status(thm)], ['84', '91'])).
% 0.20/0.60  thf('93', plain,
% 0.20/0.60      (((v4_pre_topc @ sk_B @ sk_A))
% 0.20/0.60         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & ((v2_pre_topc @ sk_A)))),
% 0.20/0.60      inference('sup+', [status(thm)], ['50', '92'])).
% 0.20/0.60  thf('94', plain,
% 0.20/0.60      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.60      inference('split', [status(esa)], ['45'])).
% 0.20/0.60  thf('95', plain,
% 0.20/0.60      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.20/0.60       ~ (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) | ~ ((v2_pre_topc @ sk_A))),
% 0.20/0.60      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.60  thf('96', plain, ($false),
% 0.20/0.60      inference('sat_resolution*', [status(thm)], ['1', '3', '48', '49', '95'])).
% 0.20/0.60  
% 0.20/0.60  % SZS output end Refutation
% 0.20/0.60  
% 0.20/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
