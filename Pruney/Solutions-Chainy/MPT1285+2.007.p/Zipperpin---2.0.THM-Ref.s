%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4PeXvUyLMg

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 383 expanded)
%              Number of leaves         :   24 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          : 1304 (7127 expanded)
%              Number of equality atoms :   32 (  82 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t107_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( v3_pre_topc @ D @ B )
                        & ( v4_tops_1 @ D @ B ) )
                     => ( v6_tops_1 @ D @ B ) )
                    & ( ( v6_tops_1 @ C @ A )
                     => ( ( v3_pre_topc @ C @ A )
                        & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( ( v3_pre_topc @ D @ B )
                          & ( v4_tops_1 @ D @ B ) )
                       => ( v6_tops_1 @ D @ B ) )
                      & ( ( v6_tops_1 @ C @ A )
                       => ( ( v3_pre_topc @ C @ A )
                          & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_tops_1])).

thf('0',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v6_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( B
              = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v6_tops_1 @ X7 @ X8 )
      | ( X7
        = ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('18',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X19 )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('25',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( v3_pre_topc @ X19 @ X18 )
        | ( ( k1_tops_1 @ X18 @ X19 )
          = X19 ) )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( v3_pre_topc @ X19 @ X18 )
        | ( ( k1_tops_1 @ X18 @ X19 )
          = X19 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('27',plain,
    ( ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('28',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ~ ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( l1_pre_topc @ X18 )
        | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
        | ~ ( v3_pre_topc @ X19 @ X18 )
        | ( ( k1_tops_1 @ X18 @ X19 )
          = X19 ) )
    | ! [X20: $i,X21: $i] :
        ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( l1_pre_topc @ X21 )
        | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X19 )
        = X19 ) ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X19 )
        = X19 ) ) ),
    inference(simpl_trail,[status(thm)],['25','33'])).

thf('35',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['22','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X6 @ ( k2_pre_topc @ X6 @ X5 ) ) @ X5 )
      | ~ ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ ( k1_tops_1 @ X6 @ X5 ) ) )
      | ( v4_tops_1 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','47'])).

thf('49',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('50',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X14 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['11','21'])).

thf('61',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('62',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('64',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('65',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['65'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( ( k1_tops_1 @ X18 @ X19 )
        = X19 ) ) ),
    inference(simpl_trail,[status(thm)],['25','33'])).

thf('72',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['67'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_tops_1 @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ ( k1_tops_1 @ X6 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ ( k1_tops_1 @ sk_B @ sk_D ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ ( k1_tops_1 @ X16 @ X15 ) @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','94'])).

thf('96',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('97',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['67'])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_tops_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_tops_1 @ X6 @ ( k2_pre_topc @ X6 @ X5 ) ) @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('106',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X7
       != ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) )
      | ( v6_tops_1 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('110',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( sk_D != sk_D )
      | ( v6_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['57'])).

thf('116',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','59','62','63','64','66','68','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4PeXvUyLMg
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 153 iterations in 0.084s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.54  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(t107_tops_1, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( l1_pre_topc @ B ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54               ( ![D:$i]:
% 0.20/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.54                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.20/0.54                       ( v6_tops_1 @ D @ B ) ) & 
% 0.20/0.54                     ( ( v6_tops_1 @ C @ A ) =>
% 0.20/0.54                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( l1_pre_topc @ B ) =>
% 0.20/0.54              ( ![C:$i]:
% 0.20/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54                  ( ![D:$i]:
% 0.20/0.54                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.54                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.20/0.54                          ( v6_tops_1 @ D @ B ) ) & 
% 0.20/0.54                        ( ( v6_tops_1 @ C @ A ) =>
% 0.20/0.54                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.20/0.54  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('2', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('4', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d8_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( v6_tops_1 @ B @ A ) <=>
% 0.20/0.54             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ~ (v6_tops_1 @ X7 @ X8)
% 0.20/0.54          | ((X7) = (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)))
% 0.20/0.54          | ~ (l1_pre_topc @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.20/0.54        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.20/0.54        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.20/0.54         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_k2_pre_topc, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54       ( m1_subset_1 @
% 0.20/0.54         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X3)
% 0.20/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.54          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf(fc9_tops_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X9 : $i, X10 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X9)
% 0.20/0.54          | ~ (v2_pre_topc @ X9)
% 0.20/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.54          | (v3_pre_topc @ (k1_tops_1 @ X9 @ X10) @ X9))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      ((v3_pre_topc @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ sk_A)),
% 0.20/0.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['11', '21'])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t55_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( l1_pre_topc @ B ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54               ( ![D:$i]:
% 0.20/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.54                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.20/0.54                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.20/0.54                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.20/0.54                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X18)
% 0.20/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54          | ~ (v3_pre_topc @ X19 @ X18)
% 0.20/0.54          | ((k1_tops_1 @ X18 @ X19) = (X19))
% 0.20/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.54          | ~ (l1_pre_topc @ X21)
% 0.20/0.54          | ~ (v2_pre_topc @ X21))),
% 0.20/0.54      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((![X18 : $i, X19 : $i]:
% 0.20/0.54          (~ (l1_pre_topc @ X18)
% 0.20/0.54           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54           | ~ (v3_pre_topc @ X19 @ X18)
% 0.20/0.54           | ((k1_tops_1 @ X18 @ X19) = (X19))))
% 0.20/0.54         <= ((![X18 : $i, X19 : $i]:
% 0.20/0.54                (~ (l1_pre_topc @ X18)
% 0.20/0.54                 | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54                 | ~ (v3_pre_topc @ X19 @ X18)
% 0.20/0.54                 | ((k1_tops_1 @ X18 @ X19) = (X19)))))),
% 0.20/0.54      inference('split', [status(esa)], ['24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      ((![X20 : $i, X21 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.54           | ~ (l1_pre_topc @ X21)
% 0.20/0.54           | ~ (v2_pre_topc @ X21)))
% 0.20/0.54         <= ((![X20 : $i, X21 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.54                 | ~ (l1_pre_topc @ X21)
% 0.20/0.54                 | ~ (v2_pre_topc @ X21))))),
% 0.20/0.54      inference('split', [status(esa)], ['24'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.54         <= ((![X20 : $i, X21 : $i]:
% 0.20/0.54                (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.54                 | ~ (l1_pre_topc @ X21)
% 0.20/0.54                 | ~ (v2_pre_topc @ X21))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (~
% 0.20/0.54       (![X20 : $i, X21 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.54           | ~ (l1_pre_topc @ X21)
% 0.20/0.54           | ~ (v2_pre_topc @ X21)))),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      ((![X18 : $i, X19 : $i]:
% 0.20/0.54          (~ (l1_pre_topc @ X18)
% 0.20/0.54           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54           | ~ (v3_pre_topc @ X19 @ X18)
% 0.20/0.54           | ((k1_tops_1 @ X18 @ X19) = (X19)))) | 
% 0.20/0.54       (![X20 : $i, X21 : $i]:
% 0.20/0.54          (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.54           | ~ (l1_pre_topc @ X21)
% 0.20/0.54           | ~ (v2_pre_topc @ X21)))),
% 0.20/0.54      inference('split', [status(esa)], ['24'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      ((![X18 : $i, X19 : $i]:
% 0.20/0.54          (~ (l1_pre_topc @ X18)
% 0.20/0.54           | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54           | ~ (v3_pre_topc @ X19 @ X18)
% 0.20/0.54           | ((k1_tops_1 @ X18 @ X19) = (X19))))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X18)
% 0.20/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54          | ~ (v3_pre_topc @ X19 @ X18)
% 0.20/0.54          | ((k1_tops_1 @ X18 @ X19) = (X19)))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['25', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.20/0.54        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '34'])).
% 0.20/0.54  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['22', '37'])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d6_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ( v4_tops_1 @ B @ A ) <=>
% 0.20/0.54             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.20/0.54               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('40', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.54          | ~ (r1_tarski @ (k1_tops_1 @ X6 @ (k2_pre_topc @ X6 @ X5)) @ X5)
% 0.20/0.54          | ~ (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ (k1_tops_1 @ X6 @ X5)))
% 0.20/0.54          | (v4_tops_1 @ X5 @ X6)
% 0.20/0.54          | ~ (l1_pre_topc @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v4_tops_1 @ sk_C @ sk_A)
% 0.20/0.54        | ~ (r1_tarski @ sk_C @ 
% 0.20/0.54             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.20/0.54        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.20/0.54             sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.54  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (((v4_tops_1 @ sk_C @ sk_A)
% 0.20/0.54        | ~ (r1_tarski @ sk_C @ 
% 0.20/0.54             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.20/0.54        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.20/0.54             sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.20/0.54         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.20/0.54              sk_C)
% 0.20/0.54         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['38', '43'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.20/0.54         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.54  thf(d10_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('47', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.20/0.54         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['44', '45', '47'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.20/0.54         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf(t44_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.54          | (r1_tarski @ (k1_tops_1 @ X14 @ X13) @ X13)
% 0.20/0.54          | ~ (l1_pre_topc @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.20/0.54           (k2_pre_topc @ sk_A @ sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.54  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.20/0.54        (k2_pre_topc @ sk_A @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.20/0.54         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['49', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['48', '55'])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.20/0.54        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.20/0.54        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['57'])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['56', '58'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['11', '21'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['57'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['4'])).
% 0.20/0.54  thf('64', plain,
% 0.20/0.54      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.20/0.54       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['57'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_D @ sk_B)
% 0.20/0.54        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.20/0.54        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.20/0.54       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['65'])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (((v4_tops_1 @ sk_D @ sk_B)
% 0.20/0.54        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.20/0.54        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.20/0.54       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['67'])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['65'])).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X18)
% 0.20/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.54          | ~ (v3_pre_topc @ X19 @ X18)
% 0.20/0.54          | ((k1_tops_1 @ X18 @ X19) = (X19)))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['25', '33'])).
% 0.20/0.54  thf('72', plain,
% 0.20/0.54      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D))
% 0.20/0.54        | ~ (v3_pre_topc @ sk_D @ sk_B)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.54  thf('73', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)) | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.20/0.54         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['69', '74'])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['67'])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.54          | ~ (v4_tops_1 @ X5 @ X6)
% 0.20/0.54          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ (k1_tops_1 @ X6 @ X5)))
% 0.20/0.54          | ~ (l1_pre_topc @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.20/0.54  thf('79', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.54        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.20/0.54        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.54  thf('80', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D)))
% 0.20/0.54        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.54  thf('82', plain,
% 0.20/0.54      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ (k1_tops_1 @ sk_B @ sk_D))))
% 0.20/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['76', '81'])).
% 0.20/0.54  thf('83', plain,
% 0.20/0.54      (((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.20/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['75', '82'])).
% 0.20/0.54  thf('84', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('85', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ X3)
% 0.20/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.54          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.20/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.20/0.54  thf('86', plain,
% 0.20/0.54      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.20/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.54  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('88', plain,
% 0.20/0.54      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.20/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.54  thf('89', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t48_tops_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_pre_topc @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.54               ( ( r1_tarski @ B @ C ) =>
% 0.20/0.54                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('90', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.54          | ~ (r1_tarski @ X15 @ X17)
% 0.20/0.54          | (r1_tarski @ (k1_tops_1 @ X16 @ X15) @ (k1_tops_1 @ X16 @ X17))
% 0.20/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.54          | ~ (l1_pre_topc @ X16))),
% 0.20/0.54      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.20/0.54  thf('91', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (l1_pre_topc @ sk_B)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54          | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ (k1_tops_1 @ sk_B @ X0))
% 0.20/0.54          | ~ (r1_tarski @ sk_D @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('92', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('93', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.54          | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ (k1_tops_1 @ sk_B @ X0))
% 0.20/0.54          | ~ (r1_tarski @ sk_D @ X0))),
% 0.20/0.54      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.54  thf('94', plain,
% 0.20/0.54      ((~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))
% 0.20/0.54        | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.20/0.54           (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['88', '93'])).
% 0.20/0.54  thf('95', plain,
% 0.20/0.54      (((r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.20/0.54         (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.20/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['83', '94'])).
% 0.20/0.54  thf('96', plain,
% 0.20/0.54      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.20/0.54         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['69', '74'])).
% 0.20/0.54  thf('97', plain,
% 0.20/0.54      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.20/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.20/0.54      inference('demod', [status(thm)], ['95', '96'])).
% 0.20/0.54  thf('98', plain,
% 0.20/0.54      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['67'])).
% 0.20/0.54  thf('99', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('100', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.54          | ~ (v4_tops_1 @ X5 @ X6)
% 0.20/0.54          | (r1_tarski @ (k1_tops_1 @ X6 @ (k2_pre_topc @ X6 @ X5)) @ X5)
% 0.20/0.54          | ~ (l1_pre_topc @ X6))),
% 0.20/0.54      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.20/0.54  thf('101', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.54        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.20/0.54        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.54  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('103', plain,
% 0.20/0.54      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.20/0.54        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['101', '102'])).
% 0.20/0.54  thf('104', plain,
% 0.20/0.54      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.20/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['98', '103'])).
% 0.20/0.54  thf('105', plain,
% 0.20/0.54      (![X0 : $i, X2 : $i]:
% 0.20/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.54  thf('106', plain,
% 0.20/0.54      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.20/0.54         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.20/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['104', '105'])).
% 0.20/0.54  thf('107', plain,
% 0.20/0.54      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.20/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['97', '106'])).
% 0.20/0.54  thf('108', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('109', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.54          | ((X7) != (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)))
% 0.20/0.54          | (v6_tops_1 @ X7 @ X8)
% 0.20/0.54          | ~ (l1_pre_topc @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.20/0.54  thf('110', plain,
% 0.20/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.54        | (v6_tops_1 @ sk_D @ sk_B)
% 0.20/0.54        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.54  thf('111', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('112', plain,
% 0.20/0.54      (((v6_tops_1 @ sk_D @ sk_B)
% 0.20/0.54        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.20/0.54      inference('demod', [status(thm)], ['110', '111'])).
% 0.20/0.54  thf('113', plain,
% 0.20/0.54      (((((sk_D) != (sk_D)) | (v6_tops_1 @ sk_D @ sk_B)))
% 0.20/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['107', '112'])).
% 0.20/0.54  thf('114', plain,
% 0.20/0.54      (((v6_tops_1 @ sk_D @ sk_B))
% 0.20/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['113'])).
% 0.20/0.54  thf('115', plain,
% 0.20/0.54      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.20/0.54      inference('split', [status(esa)], ['57'])).
% 0.20/0.54  thf('116', plain,
% 0.20/0.54      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_D @ sk_B)) | 
% 0.20/0.54       ((v6_tops_1 @ sk_D @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.54  thf('117', plain, ($false),
% 0.20/0.54      inference('sat_resolution*', [status(thm)],
% 0.20/0.54                ['1', '3', '59', '62', '63', '64', '66', '68', '116'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
