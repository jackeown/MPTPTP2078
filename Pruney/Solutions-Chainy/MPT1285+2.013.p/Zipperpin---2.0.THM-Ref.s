%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.srjrMpk0CK

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:56 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 338 expanded)
%              Number of leaves         :   24 (  99 expanded)
%              Depth                    :   17
%              Number of atoms          : 1395 (6187 expanded)
%              Number of equality atoms :   43 (  82 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v6_tops_1 @ X9 @ X10 )
      | ( X9
        = ( k1_tops_1 @ X10 @ ( k2_pre_topc @ X10 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k1_tops_1 @ X11 @ ( k1_tops_1 @ X11 @ X12 ) )
        = ( k1_tops_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('18',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('23',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) @ X7 )
      | ~ ( r1_tarski @ X7 @ ( k2_pre_topc @ X8 @ ( k1_tops_1 @ X8 @ X7 ) ) )
      | ( v4_tops_1 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ~ ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) @ sk_C )
      | ( v4_tops_1 @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_C ) ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['29','34','35','37'])).

thf('39',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v4_tops_1 @ sk_C @ sk_A )
   <= ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( v4_tops_1 @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( sk_C
      = ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k1_tops_1 @ X19 @ X18 )
       != X18 )
      | ( v3_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('45',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 )
        | ( ( k1_tops_1 @ X19 @ X18 )
         != X18 )
        | ( v3_pre_topc @ X18 @ X19 ) )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 )
        | ( ( k1_tops_1 @ X19 @ X18 )
         != X18 )
        | ( v3_pre_topc @ X18 @ X19 ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('47',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 )
        | ( ( k1_tops_1 @ X19 @ X18 )
         != X18 )
        | ( v3_pre_topc @ X18 @ X19 ) )
    | ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( ( k1_tops_1 @ X19 @ X18 )
       != X18 )
      | ( v3_pre_topc @ X18 @ X19 ) ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( ( k1_tops_1 @ X19 @ X18 )
       != X18 )
      | ( v3_pre_topc @ X18 @ X19 ) ) ),
    inference(simpl_trail,[status(thm)],['45','52'])).

thf('54',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
     != sk_C )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
     != sk_C ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( ( sk_C != sk_C )
      | ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['42','57'])).

thf('59',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('63',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('64',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_tops_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['64'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X16 )
      | ( ( k1_tops_1 @ X16 @ X17 )
        = X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('71',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( v3_pre_topc @ X17 @ X16 )
        | ( ( k1_tops_1 @ X16 @ X17 )
          = X17 ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( v3_pre_topc @ X17 @ X16 )
        | ( ( k1_tops_1 @ X16 @ X17 )
          = X17 ) ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('73',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 ) )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(split,[status(esa)],['70'])).

thf('74',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ~ ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( v3_pre_topc @ X17 @ X16 )
        | ( ( k1_tops_1 @ X16 @ X17 )
          = X17 ) )
    | ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(split,[status(esa)],['70'])).

thf('79',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X16 )
      | ( ( k1_tops_1 @ X16 @ X17 )
        = X17 ) ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X16 )
      | ( ( k1_tops_1 @ X16 @ X17 )
        = X17 ) ) ),
    inference(simpl_trail,[status(thm)],['71','79'])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['68','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('87',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
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

thf('91',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ ( k1_tops_1 @ X14 @ X13 ) @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['89','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    r1_tarski @ sk_D @ ( k2_pre_topc @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_B @ sk_D ) @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['95','100'])).

thf('102',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['84','101'])).

thf('103',plain,
    ( ( v4_tops_1 @ sk_D @ sk_B )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['66'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v4_tops_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_tops_1 @ X8 @ ( k2_pre_topc @ X8 @ X7 ) ) @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('106',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
    | ~ ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) @ sk_D )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,
    ( ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
      | ( sk_D
        = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) )
   <= ( v4_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( sk_D
      = ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X9
       != ( k1_tops_1 @ X10 @ ( k2_pre_topc @ X10 @ X9 ) ) )
      | ( v6_tops_1 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
    | ( sk_D
     != ( k1_tops_1 @ sk_B @ ( k2_pre_topc @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( sk_D != sk_D )
      | ( v6_tops_1 @ sk_D @ sk_B ) )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,
    ( ( v6_tops_1 @ sk_D @ sk_B )
   <= ( ( v4_tops_1 @ sk_D @ sk_B )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ~ ( v6_tops_1 @ sk_D @ sk_B )
   <= ~ ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['39'])).

thf('121',plain,
    ( ~ ( v4_tops_1 @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v6_tops_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','41','61','62','63','65','67','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.srjrMpk0CK
% 0.13/0.32  % Computer   : n025.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:14:51 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.38/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.54  % Solved by: fo/fo7.sh
% 0.38/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.54  % done 138 iterations in 0.106s
% 0.38/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.54  % SZS output start Refutation
% 0.38/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.54  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.38/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.38/0.54  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.38/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.38/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.54  thf(t107_tops_1, conjecture,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.54       ( ![B:$i]:
% 0.38/0.54         ( ( l1_pre_topc @ B ) =>
% 0.38/0.54           ( ![C:$i]:
% 0.38/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54               ( ![D:$i]:
% 0.38/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.54                   ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.38/0.54                       ( v6_tops_1 @ D @ B ) ) & 
% 0.38/0.54                     ( ( v6_tops_1 @ C @ A ) =>
% 0.38/0.54                       ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.54    (~( ![A:$i]:
% 0.38/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.54          ( ![B:$i]:
% 0.38/0.54            ( ( l1_pre_topc @ B ) =>
% 0.38/0.54              ( ![C:$i]:
% 0.38/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54                  ( ![D:$i]:
% 0.38/0.54                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.54                      ( ( ( ( v3_pre_topc @ D @ B ) & ( v4_tops_1 @ D @ B ) ) =>
% 0.38/0.54                          ( v6_tops_1 @ D @ B ) ) & 
% 0.38/0.54                        ( ( v6_tops_1 @ C @ A ) =>
% 0.38/0.54                          ( ( v3_pre_topc @ C @ A ) & ( v4_tops_1 @ C @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.54    inference('cnf.neg', [status(esa)], [t107_tops_1])).
% 0.38/0.54  thf('0', plain, (((v4_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('1', plain, (((v4_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('split', [status(esa)], ['0'])).
% 0.38/0.54  thf('2', plain, (((v3_pre_topc @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('3', plain,
% 0.38/0.54      (((v3_pre_topc @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('split', [status(esa)], ['2'])).
% 0.38/0.54  thf('4', plain, ((~ (v6_tops_1 @ sk_D @ sk_B) | (v6_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('5', plain,
% 0.38/0.54      (((v6_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('split', [status(esa)], ['4'])).
% 0.38/0.54  thf('6', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf(d8_tops_1, axiom,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ( l1_pre_topc @ A ) =>
% 0.38/0.54       ( ![B:$i]:
% 0.38/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54           ( ( v6_tops_1 @ B @ A ) <=>
% 0.38/0.54             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.38/0.54  thf('7', plain,
% 0.38/0.54      (![X9 : $i, X10 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.38/0.54          | ~ (v6_tops_1 @ X9 @ X10)
% 0.38/0.54          | ((X9) = (k1_tops_1 @ X10 @ (k2_pre_topc @ X10 @ X9)))
% 0.38/0.54          | ~ (l1_pre_topc @ X10))),
% 0.38/0.54      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.38/0.54  thf('8', plain,
% 0.38/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.54        | ((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.38/0.54        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.54  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('10', plain,
% 0.38/0.54      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.38/0.54        | ~ (v6_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.54  thf('11', plain,
% 0.38/0.54      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.38/0.54         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['5', '10'])).
% 0.38/0.54  thf('12', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf(dt_k2_pre_topc, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.38/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.54       ( m1_subset_1 @
% 0.38/0.54         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.54  thf('13', plain,
% 0.38/0.54      (![X3 : $i, X4 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ X3)
% 0.38/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.38/0.54          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.38/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.38/0.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.38/0.54  thf('14', plain,
% 0.38/0.54      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.38/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.54  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('16', plain,
% 0.38/0.54      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.38/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.54  thf(projectivity_k1_tops_1, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.38/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.54       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.38/0.54  thf('17', plain,
% 0.38/0.54      (![X11 : $i, X12 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ X11)
% 0.38/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.38/0.54          | ((k1_tops_1 @ X11 @ (k1_tops_1 @ X11 @ X12))
% 0.38/0.54              = (k1_tops_1 @ X11 @ X12)))),
% 0.38/0.54      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.38/0.54  thf('18', plain,
% 0.38/0.54      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.38/0.54          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.38/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.54  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('20', plain,
% 0.38/0.54      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))
% 0.38/0.54         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.38/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.38/0.54  thf('21', plain,
% 0.38/0.54      ((((k1_tops_1 @ sk_A @ sk_C)
% 0.38/0.54          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.38/0.54         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('sup+', [status(thm)], ['11', '20'])).
% 0.38/0.54  thf('22', plain,
% 0.38/0.54      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.38/0.54         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['5', '10'])).
% 0.38/0.54  thf('23', plain,
% 0.38/0.54      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.54  thf('24', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf(d6_tops_1, axiom,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ( l1_pre_topc @ A ) =>
% 0.38/0.54       ( ![B:$i]:
% 0.38/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54           ( ( v4_tops_1 @ B @ A ) <=>
% 0.38/0.54             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.38/0.54               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.38/0.54  thf('25', plain,
% 0.38/0.54      (![X7 : $i, X8 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.38/0.54          | ~ (r1_tarski @ (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)) @ X7)
% 0.38/0.54          | ~ (r1_tarski @ X7 @ (k2_pre_topc @ X8 @ (k1_tops_1 @ X8 @ X7)))
% 0.38/0.54          | (v4_tops_1 @ X7 @ X8)
% 0.38/0.54          | ~ (l1_pre_topc @ X8))),
% 0.38/0.54      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.38/0.54  thf('26', plain,
% 0.38/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.54        | (v4_tops_1 @ sk_C @ sk_A)
% 0.38/0.54        | ~ (r1_tarski @ sk_C @ 
% 0.38/0.54             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.38/0.54        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.38/0.54             sk_C))),
% 0.38/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.54  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('28', plain,
% 0.38/0.54      (((v4_tops_1 @ sk_C @ sk_A)
% 0.38/0.54        | ~ (r1_tarski @ sk_C @ 
% 0.38/0.54             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.38/0.54        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.38/0.54             sk_C))),
% 0.38/0.54      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.54  thf('29', plain,
% 0.38/0.54      (((~ (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))
% 0.38/0.54         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C)) @ 
% 0.38/0.54              sk_C)
% 0.38/0.54         | (v4_tops_1 @ sk_C @ sk_A))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['23', '28'])).
% 0.38/0.54  thf('30', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf(t48_pre_topc, axiom,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ( l1_pre_topc @ A ) =>
% 0.38/0.54       ( ![B:$i]:
% 0.38/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.38/0.54  thf('31', plain,
% 0.38/0.54      (![X5 : $i, X6 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.38/0.54          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ X5))
% 0.38/0.54          | ~ (l1_pre_topc @ X6))),
% 0.38/0.54      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.38/0.54  thf('32', plain,
% 0.38/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.54        | (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.54  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('34', plain, ((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.38/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.54  thf('35', plain,
% 0.38/0.54      ((((sk_C) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_C))))
% 0.38/0.54         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['5', '10'])).
% 0.38/0.54  thf(d10_xboole_0, axiom,
% 0.38/0.54    (![A:$i,B:$i]:
% 0.38/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.54  thf('36', plain,
% 0.38/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.54  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.54      inference('simplify', [status(thm)], ['36'])).
% 0.38/0.54  thf('38', plain,
% 0.38/0.54      (((v4_tops_1 @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('demod', [status(thm)], ['29', '34', '35', '37'])).
% 0.38/0.54  thf('39', plain,
% 0.38/0.54      ((~ (v6_tops_1 @ sk_D @ sk_B)
% 0.38/0.54        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.38/0.54        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('40', plain,
% 0.38/0.54      ((~ (v4_tops_1 @ sk_C @ sk_A)) <= (~ ((v4_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('split', [status(esa)], ['39'])).
% 0.38/0.54  thf('41', plain,
% 0.38/0.54      (((v4_tops_1 @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['38', '40'])).
% 0.38/0.54  thf('42', plain,
% 0.38/0.54      ((((sk_C) = (k1_tops_1 @ sk_A @ sk_C))) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.54  thf('43', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf(t55_tops_1, axiom,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.54       ( ![B:$i]:
% 0.38/0.54         ( ( l1_pre_topc @ B ) =>
% 0.38/0.54           ( ![C:$i]:
% 0.38/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54               ( ![D:$i]:
% 0.38/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.38/0.54                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.38/0.54                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.38/0.54                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.38/0.54                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.54  thf('44', plain,
% 0.38/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ X16)
% 0.38/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.54          | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.38/0.54          | (v3_pre_topc @ X18 @ X19)
% 0.38/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54          | ~ (l1_pre_topc @ X19)
% 0.38/0.54          | ~ (v2_pre_topc @ X19))),
% 0.38/0.54      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.38/0.54  thf('45', plain,
% 0.38/0.54      ((![X18 : $i, X19 : $i]:
% 0.38/0.54          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54           | ~ (l1_pre_topc @ X19)
% 0.38/0.54           | ~ (v2_pre_topc @ X19)
% 0.38/0.54           | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.38/0.54           | (v3_pre_topc @ X18 @ X19)))
% 0.38/0.54         <= ((![X18 : $i, X19 : $i]:
% 0.38/0.54                (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54                 | ~ (l1_pre_topc @ X19)
% 0.38/0.54                 | ~ (v2_pre_topc @ X19)
% 0.38/0.54                 | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.38/0.54                 | (v3_pre_topc @ X18 @ X19))))),
% 0.38/0.54      inference('split', [status(esa)], ['44'])).
% 0.38/0.54  thf('46', plain,
% 0.38/0.54      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.38/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.54  thf('47', plain,
% 0.38/0.54      ((![X16 : $i, X17 : $i]:
% 0.38/0.54          (~ (l1_pre_topc @ X16)
% 0.38/0.54           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))))
% 0.38/0.54         <= ((![X16 : $i, X17 : $i]:
% 0.38/0.54                (~ (l1_pre_topc @ X16)
% 0.38/0.54                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))))),
% 0.38/0.54      inference('split', [status(esa)], ['44'])).
% 0.38/0.54  thf('48', plain,
% 0.38/0.54      ((~ (l1_pre_topc @ sk_A))
% 0.38/0.54         <= ((![X16 : $i, X17 : $i]:
% 0.38/0.54                (~ (l1_pre_topc @ X16)
% 0.38/0.54                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))))),
% 0.38/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.54  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('50', plain,
% 0.38/0.54      (~
% 0.38/0.54       (![X16 : $i, X17 : $i]:
% 0.38/0.54          (~ (l1_pre_topc @ X16)
% 0.38/0.54           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))))),
% 0.38/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.54  thf('51', plain,
% 0.38/0.54      ((![X18 : $i, X19 : $i]:
% 0.38/0.54          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54           | ~ (l1_pre_topc @ X19)
% 0.38/0.54           | ~ (v2_pre_topc @ X19)
% 0.38/0.54           | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.38/0.54           | (v3_pre_topc @ X18 @ X19))) | 
% 0.38/0.54       (![X16 : $i, X17 : $i]:
% 0.38/0.54          (~ (l1_pre_topc @ X16)
% 0.38/0.54           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))))),
% 0.38/0.54      inference('split', [status(esa)], ['44'])).
% 0.38/0.54  thf('52', plain,
% 0.38/0.54      ((![X18 : $i, X19 : $i]:
% 0.38/0.54          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54           | ~ (l1_pre_topc @ X19)
% 0.38/0.54           | ~ (v2_pre_topc @ X19)
% 0.38/0.54           | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.38/0.54           | (v3_pre_topc @ X18 @ X19)))),
% 0.38/0.54      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.38/0.54  thf('53', plain,
% 0.38/0.54      (![X18 : $i, X19 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54          | ~ (l1_pre_topc @ X19)
% 0.38/0.54          | ~ (v2_pre_topc @ X19)
% 0.38/0.54          | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.38/0.54          | (v3_pre_topc @ X18 @ X19))),
% 0.38/0.54      inference('simpl_trail', [status(thm)], ['45', '52'])).
% 0.38/0.54  thf('54', plain,
% 0.38/0.54      (((v3_pre_topc @ sk_C @ sk_A)
% 0.38/0.54        | ((k1_tops_1 @ sk_A @ sk_C) != (sk_C))
% 0.38/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['43', '53'])).
% 0.38/0.54  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('57', plain,
% 0.38/0.54      (((v3_pre_topc @ sk_C @ sk_A) | ((k1_tops_1 @ sk_A @ sk_C) != (sk_C)))),
% 0.38/0.54      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.38/0.54  thf('58', plain,
% 0.38/0.54      (((((sk_C) != (sk_C)) | (v3_pre_topc @ sk_C @ sk_A)))
% 0.38/0.54         <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['42', '57'])).
% 0.38/0.54  thf('59', plain,
% 0.38/0.54      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v6_tops_1 @ sk_C @ sk_A)))),
% 0.38/0.54      inference('simplify', [status(thm)], ['58'])).
% 0.38/0.54  thf('60', plain,
% 0.38/0.54      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.38/0.54      inference('split', [status(esa)], ['39'])).
% 0.38/0.54  thf('61', plain,
% 0.38/0.54      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v6_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('sup-', [status(thm)], ['59', '60'])).
% 0.38/0.54  thf('62', plain,
% 0.38/0.54      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ((v6_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('split', [status(esa)], ['4'])).
% 0.38/0.54  thf('63', plain,
% 0.38/0.54      (~ ((v6_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.38/0.54       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('split', [status(esa)], ['39'])).
% 0.38/0.54  thf('64', plain,
% 0.38/0.54      (((v3_pre_topc @ sk_D @ sk_B)
% 0.38/0.54        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.38/0.54        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('65', plain,
% 0.38/0.54      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.38/0.54       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('split', [status(esa)], ['64'])).
% 0.38/0.54  thf('66', plain,
% 0.38/0.54      (((v4_tops_1 @ sk_D @ sk_B)
% 0.38/0.54        | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.38/0.54        | ~ (v4_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('67', plain,
% 0.38/0.54      (((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.38/0.54       ~ ((v4_tops_1 @ sk_C @ sk_A))),
% 0.38/0.54      inference('split', [status(esa)], ['66'])).
% 0.38/0.54  thf('68', plain,
% 0.38/0.54      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.38/0.54      inference('split', [status(esa)], ['64'])).
% 0.38/0.54  thf('69', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('70', plain,
% 0.38/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ X16)
% 0.38/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.54          | ~ (v3_pre_topc @ X17 @ X16)
% 0.38/0.54          | ((k1_tops_1 @ X16 @ X17) = (X17))
% 0.38/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54          | ~ (l1_pre_topc @ X19)
% 0.38/0.54          | ~ (v2_pre_topc @ X19))),
% 0.38/0.54      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.38/0.54  thf('71', plain,
% 0.38/0.54      ((![X16 : $i, X17 : $i]:
% 0.38/0.54          (~ (l1_pre_topc @ X16)
% 0.38/0.54           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.54           | ~ (v3_pre_topc @ X17 @ X16)
% 0.38/0.54           | ((k1_tops_1 @ X16 @ X17) = (X17))))
% 0.38/0.54         <= ((![X16 : $i, X17 : $i]:
% 0.38/0.54                (~ (l1_pre_topc @ X16)
% 0.38/0.54                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.54                 | ~ (v3_pre_topc @ X17 @ X16)
% 0.38/0.54                 | ((k1_tops_1 @ X16 @ X17) = (X17)))))),
% 0.38/0.54      inference('split', [status(esa)], ['70'])).
% 0.38/0.54  thf('72', plain,
% 0.38/0.54      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.38/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.54      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.54  thf('73', plain,
% 0.38/0.54      ((![X18 : $i, X19 : $i]:
% 0.38/0.54          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54           | ~ (l1_pre_topc @ X19)
% 0.38/0.54           | ~ (v2_pre_topc @ X19)))
% 0.38/0.54         <= ((![X18 : $i, X19 : $i]:
% 0.38/0.54                (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54                 | ~ (l1_pre_topc @ X19)
% 0.38/0.54                 | ~ (v2_pre_topc @ X19))))),
% 0.38/0.54      inference('split', [status(esa)], ['70'])).
% 0.38/0.54  thf('74', plain,
% 0.38/0.54      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.38/0.54         <= ((![X18 : $i, X19 : $i]:
% 0.38/0.54                (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54                 | ~ (l1_pre_topc @ X19)
% 0.38/0.54                 | ~ (v2_pre_topc @ X19))))),
% 0.38/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.38/0.54  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('77', plain,
% 0.38/0.54      (~
% 0.38/0.54       (![X18 : $i, X19 : $i]:
% 0.38/0.54          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54           | ~ (l1_pre_topc @ X19)
% 0.38/0.54           | ~ (v2_pre_topc @ X19)))),
% 0.38/0.54      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.38/0.54  thf('78', plain,
% 0.38/0.54      ((![X16 : $i, X17 : $i]:
% 0.38/0.54          (~ (l1_pre_topc @ X16)
% 0.38/0.54           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.54           | ~ (v3_pre_topc @ X17 @ X16)
% 0.38/0.54           | ((k1_tops_1 @ X16 @ X17) = (X17)))) | 
% 0.38/0.54       (![X18 : $i, X19 : $i]:
% 0.38/0.54          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.38/0.54           | ~ (l1_pre_topc @ X19)
% 0.38/0.54           | ~ (v2_pre_topc @ X19)))),
% 0.38/0.54      inference('split', [status(esa)], ['70'])).
% 0.38/0.54  thf('79', plain,
% 0.38/0.54      ((![X16 : $i, X17 : $i]:
% 0.38/0.54          (~ (l1_pre_topc @ X16)
% 0.38/0.54           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.54           | ~ (v3_pre_topc @ X17 @ X16)
% 0.38/0.54           | ((k1_tops_1 @ X16 @ X17) = (X17))))),
% 0.38/0.54      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.38/0.54  thf('80', plain,
% 0.38/0.54      (![X16 : $i, X17 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ X16)
% 0.38/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.54          | ~ (v3_pre_topc @ X17 @ X16)
% 0.38/0.54          | ((k1_tops_1 @ X16 @ X17) = (X17)))),
% 0.38/0.54      inference('simpl_trail', [status(thm)], ['71', '79'])).
% 0.38/0.54  thf('81', plain,
% 0.38/0.54      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D))
% 0.38/0.54        | ~ (v3_pre_topc @ sk_D @ sk_B)
% 0.38/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.38/0.54      inference('sup-', [status(thm)], ['69', '80'])).
% 0.38/0.54  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('83', plain,
% 0.38/0.54      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)) | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.38/0.54      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.54  thf('84', plain,
% 0.38/0.54      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.38/0.54         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['68', '83'])).
% 0.38/0.54  thf('85', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('86', plain,
% 0.38/0.54      (![X3 : $i, X4 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ X3)
% 0.38/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.38/0.54          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.38/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.38/0.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.38/0.54  thf('87', plain,
% 0.38/0.54      (((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.38/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.54        | ~ (l1_pre_topc @ sk_B))),
% 0.38/0.54      inference('sup-', [status(thm)], ['85', '86'])).
% 0.38/0.54  thf('88', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('89', plain,
% 0.38/0.54      ((m1_subset_1 @ (k2_pre_topc @ sk_B @ sk_D) @ 
% 0.38/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.54      inference('demod', [status(thm)], ['87', '88'])).
% 0.38/0.54  thf('90', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf(t48_tops_1, axiom,
% 0.38/0.54    (![A:$i]:
% 0.38/0.54     ( ( l1_pre_topc @ A ) =>
% 0.38/0.54       ( ![B:$i]:
% 0.38/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54           ( ![C:$i]:
% 0.38/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.54               ( ( r1_tarski @ B @ C ) =>
% 0.38/0.54                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.38/0.54  thf('91', plain,
% 0.38/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.54          | ~ (r1_tarski @ X13 @ X15)
% 0.38/0.54          | (r1_tarski @ (k1_tops_1 @ X14 @ X13) @ (k1_tops_1 @ X14 @ X15))
% 0.38/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.38/0.54          | ~ (l1_pre_topc @ X14))),
% 0.38/0.54      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.38/0.54  thf('92', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (l1_pre_topc @ sk_B)
% 0.38/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.54          | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ (k1_tops_1 @ sk_B @ X0))
% 0.38/0.54          | ~ (r1_tarski @ sk_D @ X0))),
% 0.38/0.54      inference('sup-', [status(thm)], ['90', '91'])).
% 0.38/0.54  thf('93', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('94', plain,
% 0.38/0.54      (![X0 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.38/0.54          | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ (k1_tops_1 @ sk_B @ X0))
% 0.38/0.54          | ~ (r1_tarski @ sk_D @ X0))),
% 0.38/0.54      inference('demod', [status(thm)], ['92', '93'])).
% 0.38/0.54  thf('95', plain,
% 0.38/0.54      ((~ (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))
% 0.38/0.54        | (r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.38/0.54           (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.38/0.54      inference('sup-', [status(thm)], ['89', '94'])).
% 0.38/0.54  thf('96', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('97', plain,
% 0.38/0.54      (![X5 : $i, X6 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.38/0.54          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ X5))
% 0.38/0.54          | ~ (l1_pre_topc @ X6))),
% 0.38/0.54      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.38/0.54  thf('98', plain,
% 0.38/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.38/0.54        | (r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['96', '97'])).
% 0.38/0.54  thf('99', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('100', plain, ((r1_tarski @ sk_D @ (k2_pre_topc @ sk_B @ sk_D))),
% 0.38/0.54      inference('demod', [status(thm)], ['98', '99'])).
% 0.38/0.54  thf('101', plain,
% 0.38/0.54      ((r1_tarski @ (k1_tops_1 @ sk_B @ sk_D) @ 
% 0.38/0.54        (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))),
% 0.38/0.54      inference('demod', [status(thm)], ['95', '100'])).
% 0.38/0.54  thf('102', plain,
% 0.38/0.54      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.38/0.54         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.38/0.54      inference('sup+', [status(thm)], ['84', '101'])).
% 0.38/0.54  thf('103', plain,
% 0.38/0.54      (((v4_tops_1 @ sk_D @ sk_B)) <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.38/0.54      inference('split', [status(esa)], ['66'])).
% 0.38/0.54  thf('104', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('105', plain,
% 0.38/0.54      (![X7 : $i, X8 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.38/0.54          | ~ (v4_tops_1 @ X7 @ X8)
% 0.38/0.54          | (r1_tarski @ (k1_tops_1 @ X8 @ (k2_pre_topc @ X8 @ X7)) @ X7)
% 0.38/0.54          | ~ (l1_pre_topc @ X8))),
% 0.38/0.54      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.38/0.54  thf('106', plain,
% 0.38/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.38/0.54        | (r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.38/0.54        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.38/0.54      inference('sup-', [status(thm)], ['104', '105'])).
% 0.38/0.54  thf('107', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('108', plain,
% 0.38/0.54      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D)
% 0.38/0.54        | ~ (v4_tops_1 @ sk_D @ sk_B))),
% 0.38/0.54      inference('demod', [status(thm)], ['106', '107'])).
% 0.38/0.54  thf('109', plain,
% 0.38/0.54      (((r1_tarski @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)) @ sk_D))
% 0.38/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['103', '108'])).
% 0.38/0.54  thf('110', plain,
% 0.38/0.54      (![X0 : $i, X2 : $i]:
% 0.38/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.54  thf('111', plain,
% 0.38/0.54      (((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))
% 0.38/0.54         | ((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D)))))
% 0.38/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['109', '110'])).
% 0.38/0.54  thf('112', plain,
% 0.38/0.54      ((((sk_D) = (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))
% 0.38/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['102', '111'])).
% 0.38/0.54  thf('113', plain,
% 0.38/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('114', plain,
% 0.38/0.54      (![X9 : $i, X10 : $i]:
% 0.38/0.54         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.38/0.54          | ((X9) != (k1_tops_1 @ X10 @ (k2_pre_topc @ X10 @ X9)))
% 0.38/0.54          | (v6_tops_1 @ X9 @ X10)
% 0.38/0.54          | ~ (l1_pre_topc @ X10))),
% 0.38/0.54      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.38/0.54  thf('115', plain,
% 0.38/0.54      ((~ (l1_pre_topc @ sk_B)
% 0.38/0.54        | (v6_tops_1 @ sk_D @ sk_B)
% 0.38/0.54        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.38/0.54      inference('sup-', [status(thm)], ['113', '114'])).
% 0.38/0.54  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.38/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.54  thf('117', plain,
% 0.38/0.54      (((v6_tops_1 @ sk_D @ sk_B)
% 0.38/0.54        | ((sk_D) != (k1_tops_1 @ sk_B @ (k2_pre_topc @ sk_B @ sk_D))))),
% 0.38/0.54      inference('demod', [status(thm)], ['115', '116'])).
% 0.38/0.54  thf('118', plain,
% 0.38/0.54      (((((sk_D) != (sk_D)) | (v6_tops_1 @ sk_D @ sk_B)))
% 0.38/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.38/0.54      inference('sup-', [status(thm)], ['112', '117'])).
% 0.38/0.54  thf('119', plain,
% 0.38/0.54      (((v6_tops_1 @ sk_D @ sk_B))
% 0.38/0.54         <= (((v4_tops_1 @ sk_D @ sk_B)) & ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.38/0.54      inference('simplify', [status(thm)], ['118'])).
% 0.38/0.54  thf('120', plain,
% 0.38/0.54      ((~ (v6_tops_1 @ sk_D @ sk_B)) <= (~ ((v6_tops_1 @ sk_D @ sk_B)))),
% 0.38/0.54      inference('split', [status(esa)], ['39'])).
% 0.38/0.54  thf('121', plain,
% 0.38/0.54      (~ ((v4_tops_1 @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_D @ sk_B)) | 
% 0.38/0.54       ((v6_tops_1 @ sk_D @ sk_B))),
% 0.38/0.54      inference('sup-', [status(thm)], ['119', '120'])).
% 0.38/0.54  thf('122', plain, ($false),
% 0.38/0.54      inference('sat_resolution*', [status(thm)],
% 0.38/0.54                ['1', '3', '41', '61', '62', '63', '65', '67', '121'])).
% 0.38/0.54  
% 0.38/0.54  % SZS output end Refutation
% 0.38/0.54  
% 0.38/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
