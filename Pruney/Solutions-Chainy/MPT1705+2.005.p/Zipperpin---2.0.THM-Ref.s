%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KGhYyhBFzl

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:09 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  205 (1550 expanded)
%              Number of leaves         :   29 ( 462 expanded)
%              Depth                    :   22
%              Number of atoms          : 1741 (25341 expanded)
%              Number of equality atoms :   41 ( 750 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(t14_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_tsep_1 @ C @ A )
                    & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v2_pre_topc @ C )
                  & ( l1_pre_topc @ C ) )
               => ( ( C
                    = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                 => ( ( ( v1_tsep_1 @ B @ A )
                      & ( m1_pre_topc @ B @ A ) )
                  <=> ( ( v1_tsep_1 @ C @ A )
                      & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_tmap_1])).

thf('0',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( X14
       != ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_pre_topc @ X14 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14','15','16'])).

thf('18',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( X14
       != ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X16 )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) @ X16 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_C )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32','33','34'])).

thf('36',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
   <= ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('45',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( v3_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v1_tsep_1 @ sk_C @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','54'])).

thf('56',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('57',plain,(
    ! [X13: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('58',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('59',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('60',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('61',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_pre_topc @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('76',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','77'])).

thf('79',plain,(
    ! [X13: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf('80',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('82',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_pre_topc @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ X12 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) )
      | ( v3_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('95',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,
    ( ~ ( v2_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C )
    | ~ ( l1_struct_0 @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('108',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105','108'])).

thf('110',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('111',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','111'])).

thf('113',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('114',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('115',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ~ ( v3_pre_topc @ X19 @ X18 )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('119',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['112','124'])).

thf('126',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( ( v1_tsep_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','125'])).

thf('127',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('128',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ~ ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','4','22','40','128'])).

thf('130',plain,(
    ~ ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','129'])).

thf('131',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('132',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('133',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('137',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('143',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','111'])).

thf('144',plain,
    ( ( ( u1_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['75','76'])).

thf('146',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['141','146'])).

thf('148',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','22'])).

thf('149',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A )
    | ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('151',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('152',plain,
    ( ( ( k2_struct_0 @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['106','107'])).

thf('154',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('156',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('157',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X17 ) @ X18 )
      | ~ ( v1_tsep_1 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('158',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v1_tsep_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('160',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['158','159','160','161'])).

thf('163',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','162'])).

thf('164',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','111'])).

thf('165',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('166',plain,
    ( ( v3_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('168',plain,(
    v1_tsep_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','4','22','40','128','167'])).

thf('169',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['4','22','40'])).

thf('170',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['166','168','169'])).

thf('171',plain,
    ( ( k2_struct_0 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('172',plain,(
    v3_pre_topc @ ( k2_struct_0 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    v1_tsep_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['149','154','172'])).

thf('174',plain,(
    $false ),
    inference(demod,[status(thm)],['130','173'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KGhYyhBFzl
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:36:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.50/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.67  % Solved by: fo/fo7.sh
% 0.50/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.67  % done 437 iterations in 0.219s
% 0.50/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.67  % SZS output start Refutation
% 0.50/0.67  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.50/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.67  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.50/0.67  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.50/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.67  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.50/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.50/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.67  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.50/0.67  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.50/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.50/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.50/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.50/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.50/0.67  thf(t14_tmap_1, conjecture,
% 0.50/0.67    (![A:$i]:
% 0.50/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.67       ( ![B:$i]:
% 0.50/0.67         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.50/0.67           ( ![C:$i]:
% 0.50/0.67             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.50/0.67               ( ( ( C ) =
% 0.50/0.67                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.50/0.67                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.50/0.67                   ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.50/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.67    (~( ![A:$i]:
% 0.50/0.67        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.67          ( ![B:$i]:
% 0.50/0.67            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.50/0.67              ( ![C:$i]:
% 0.50/0.67                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.50/0.67                  ( ( ( C ) =
% 0.50/0.67                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.50/0.67                    ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.50/0.67                      ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.50/0.67    inference('cnf.neg', [status(esa)], [t14_tmap_1])).
% 0.50/0.67  thf('0', plain,
% 0.50/0.67      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.50/0.67        | ~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.50/0.67        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.50/0.67        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('1', plain,
% 0.50/0.67      ((~ (v1_tsep_1 @ sk_C @ sk_A)) <= (~ ((v1_tsep_1 @ sk_C @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['0'])).
% 0.50/0.67  thf('2', plain,
% 0.50/0.67      (~ ((v1_tsep_1 @ sk_C @ sk_A)) | ~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.50/0.67       ~ ((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.50/0.67      inference('split', [status(esa)], ['0'])).
% 0.50/0.67  thf('3', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('4', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_B @ sk_A)) | ((m1_pre_topc @ sk_C @ sk_A))),
% 0.50/0.67      inference('split', [status(esa)], ['3'])).
% 0.50/0.67  thf('5', plain, (((v1_tsep_1 @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('6', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['5'])).
% 0.50/0.67  thf('7', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf(t12_tmap_1, axiom,
% 0.50/0.67    (![A:$i]:
% 0.50/0.67     ( ( l1_pre_topc @ A ) =>
% 0.50/0.67       ( ![B:$i]:
% 0.50/0.67         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.50/0.67           ( ![C:$i]:
% 0.50/0.67             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.50/0.67               ( ( ( B ) =
% 0.50/0.67                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.50/0.67                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.50/0.67  thf('8', plain,
% 0.50/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X14)
% 0.50/0.67          | ~ (l1_pre_topc @ X14)
% 0.50/0.67          | ((X14) != (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.50/0.67          | ~ (m1_pre_topc @ X15 @ X16)
% 0.50/0.67          | (m1_pre_topc @ X14 @ X16)
% 0.50/0.67          | ~ (l1_pre_topc @ X15)
% 0.50/0.67          | ~ (v2_pre_topc @ X15)
% 0.50/0.67          | ~ (l1_pre_topc @ X16))),
% 0.50/0.67      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.50/0.67  thf('9', plain,
% 0.50/0.67      (![X15 : $i, X16 : $i]:
% 0.50/0.67         (~ (l1_pre_topc @ X16)
% 0.50/0.67          | ~ (v2_pre_topc @ X15)
% 0.50/0.67          | ~ (l1_pre_topc @ X15)
% 0.50/0.67          | (m1_pre_topc @ 
% 0.50/0.67             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)) @ X16)
% 0.50/0.67          | ~ (m1_pre_topc @ X15 @ X16)
% 0.50/0.67          | ~ (l1_pre_topc @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.50/0.67          | ~ (v2_pre_topc @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15))))),
% 0.50/0.67      inference('simplify', [status(thm)], ['8'])).
% 0.50/0.67  thf('10', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (l1_pre_topc @ sk_C)
% 0.50/0.67          | ~ (v2_pre_topc @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.50/0.67          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.50/0.67          | (m1_pre_topc @ 
% 0.50/0.67             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.67          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.67          | ~ (l1_pre_topc @ X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['7', '9'])).
% 0.50/0.67  thf('11', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('12', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('13', plain, ((v2_pre_topc @ sk_C)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('14', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('16', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('17', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (m1_pre_topc @ sk_B @ X0)
% 0.50/0.67          | (m1_pre_topc @ sk_C @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0))),
% 0.50/0.67      inference('demod', [status(thm)],
% 0.50/0.67                ['10', '11', '12', '13', '14', '15', '16'])).
% 0.50/0.67  thf('18', plain,
% 0.50/0.67      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_C @ sk_A)))
% 0.50/0.67         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['6', '17'])).
% 0.50/0.67  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('20', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['18', '19'])).
% 0.50/0.67  thf('21', plain,
% 0.50/0.67      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['0'])).
% 0.50/0.67  thf('22', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.50/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.50/0.67  thf('23', plain, (((m1_pre_topc @ sk_C @ sk_A) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('24', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['23'])).
% 0.50/0.67  thf('25', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('26', plain,
% 0.50/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X14)
% 0.50/0.67          | ~ (l1_pre_topc @ X14)
% 0.50/0.67          | ((X14) != (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.50/0.67          | ~ (m1_pre_topc @ X14 @ X16)
% 0.50/0.67          | (m1_pre_topc @ X15 @ X16)
% 0.50/0.67          | ~ (l1_pre_topc @ X15)
% 0.50/0.67          | ~ (v2_pre_topc @ X15)
% 0.50/0.67          | ~ (l1_pre_topc @ X16))),
% 0.50/0.67      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.50/0.67  thf('27', plain,
% 0.50/0.67      (![X15 : $i, X16 : $i]:
% 0.50/0.67         (~ (l1_pre_topc @ X16)
% 0.50/0.67          | ~ (v2_pre_topc @ X15)
% 0.50/0.67          | ~ (l1_pre_topc @ X15)
% 0.50/0.67          | (m1_pre_topc @ X15 @ X16)
% 0.50/0.67          | ~ (m1_pre_topc @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)) @ X16)
% 0.50/0.67          | ~ (l1_pre_topc @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.50/0.67          | ~ (v2_pre_topc @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15))))),
% 0.50/0.67      inference('simplify', [status(thm)], ['26'])).
% 0.50/0.67  thf('28', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (l1_pre_topc @ sk_C)
% 0.50/0.67          | ~ (v2_pre_topc @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.50/0.67          | ~ (m1_pre_topc @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.50/0.67          | (m1_pre_topc @ sk_B @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ sk_B)
% 0.50/0.67          | ~ (v2_pre_topc @ sk_B)
% 0.50/0.67          | ~ (l1_pre_topc @ X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['25', '27'])).
% 0.50/0.67  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('30', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('31', plain, ((v2_pre_topc @ sk_C)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('32', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('34', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('35', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (m1_pre_topc @ sk_C @ X0)
% 0.50/0.67          | (m1_pre_topc @ sk_B @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0))),
% 0.50/0.67      inference('demod', [status(thm)],
% 0.50/0.67                ['28', '29', '30', '31', '32', '33', '34'])).
% 0.50/0.67  thf('36', plain,
% 0.50/0.67      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A)))
% 0.50/0.67         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['24', '35'])).
% 0.50/0.67  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('38', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['36', '37'])).
% 0.50/0.67  thf('39', plain,
% 0.50/0.67      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['0'])).
% 0.50/0.67  thf('40', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.50/0.67      inference('sup-', [status(thm)], ['38', '39'])).
% 0.50/0.67  thf('41', plain, (((v1_tsep_1 @ sk_C @ sk_A) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('42', plain,
% 0.50/0.67      (((v1_tsep_1 @ sk_C @ sk_A)) <= (((v1_tsep_1 @ sk_C @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['41'])).
% 0.50/0.67  thf('43', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['18', '19'])).
% 0.50/0.67  thf(t1_tsep_1, axiom,
% 0.50/0.67    (![A:$i]:
% 0.50/0.67     ( ( l1_pre_topc @ A ) =>
% 0.50/0.67       ( ![B:$i]:
% 0.50/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.50/0.67           ( m1_subset_1 @
% 0.50/0.67             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.50/0.67  thf('44', plain,
% 0.50/0.67      (![X20 : $i, X21 : $i]:
% 0.50/0.67         (~ (m1_pre_topc @ X20 @ X21)
% 0.50/0.67          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.50/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.50/0.67          | ~ (l1_pre_topc @ X21))),
% 0.50/0.67      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.50/0.67  thf('45', plain,
% 0.50/0.67      (((~ (l1_pre_topc @ sk_A)
% 0.50/0.67         | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.50/0.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.50/0.67         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.50/0.67  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('47', plain,
% 0.50/0.67      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.50/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.50/0.67         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.50/0.67  thf(t16_tsep_1, axiom,
% 0.50/0.67    (![A:$i]:
% 0.50/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.67       ( ![B:$i]:
% 0.50/0.67         ( ( m1_pre_topc @ B @ A ) =>
% 0.50/0.67           ( ![C:$i]:
% 0.50/0.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.67               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.50/0.67                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.50/0.67                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.50/0.67  thf('48', plain,
% 0.50/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.67         (~ (m1_pre_topc @ X17 @ X18)
% 0.50/0.67          | ((X19) != (u1_struct_0 @ X17))
% 0.50/0.67          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.50/0.67          | ~ (m1_pre_topc @ X17 @ X18)
% 0.50/0.67          | (v3_pre_topc @ X19 @ X18)
% 0.50/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.50/0.67          | ~ (l1_pre_topc @ X18)
% 0.50/0.67          | ~ (v2_pre_topc @ X18))),
% 0.50/0.67      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.50/0.67  thf('49', plain,
% 0.50/0.67      (![X17 : $i, X18 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X18)
% 0.50/0.67          | ~ (l1_pre_topc @ X18)
% 0.50/0.67          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.50/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.50/0.67          | (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.50/0.67          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.50/0.67          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.50/0.67      inference('simplify', [status(thm)], ['48'])).
% 0.50/0.67  thf('50', plain,
% 0.50/0.67      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.50/0.67         | ~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.50/0.67         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.50/0.67         | ~ (l1_pre_topc @ sk_A)
% 0.50/0.67         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['47', '49'])).
% 0.50/0.67  thf('51', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['18', '19'])).
% 0.50/0.67  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('54', plain,
% 0.50/0.67      (((~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.50/0.67         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.50/0.67         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.50/0.67  thf('55', plain,
% 0.50/0.67      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.50/0.67         <= (((v1_tsep_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['42', '54'])).
% 0.50/0.67  thf('56', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf(fc10_tops_1, axiom,
% 0.50/0.67    (![A:$i]:
% 0.50/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.67       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.50/0.67  thf('57', plain,
% 0.50/0.67      (![X13 : $i]:
% 0.50/0.67         ((v3_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 0.50/0.67          | ~ (l1_pre_topc @ X13)
% 0.50/0.67          | ~ (v2_pre_topc @ X13))),
% 0.50/0.67      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.50/0.67  thf(d3_struct_0, axiom,
% 0.50/0.67    (![A:$i]:
% 0.50/0.67     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.50/0.67  thf('58', plain,
% 0.50/0.67      (![X8 : $i]:
% 0.50/0.67         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.50/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.67  thf(dt_k2_subset_1, axiom,
% 0.50/0.67    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.50/0.67  thf('59', plain,
% 0.50/0.67      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.50/0.67      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.50/0.67  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.50/0.67  thf('60', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.50/0.67      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.50/0.67  thf('61', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.50/0.67      inference('demod', [status(thm)], ['59', '60'])).
% 0.50/0.67  thf(t60_pre_topc, axiom,
% 0.50/0.67    (![A:$i]:
% 0.50/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.50/0.67       ( ![B:$i]:
% 0.50/0.67         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.50/0.67             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.50/0.67           ( ( v3_pre_topc @
% 0.50/0.67               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.50/0.67             ( m1_subset_1 @
% 0.50/0.67               B @ 
% 0.50/0.67               ( k1_zfmisc_1 @
% 0.50/0.67                 ( u1_struct_0 @
% 0.50/0.67                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.50/0.67  thf('62', plain,
% 0.50/0.67      (![X11 : $i, X12 : $i]:
% 0.50/0.67         (~ (v3_pre_topc @ X12 @ X11)
% 0.50/0.67          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.50/0.67          | (m1_subset_1 @ X12 @ 
% 0.50/0.67             (k1_zfmisc_1 @ 
% 0.50/0.67              (u1_struct_0 @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))))
% 0.50/0.67          | ~ (l1_pre_topc @ X11)
% 0.50/0.67          | ~ (v2_pre_topc @ X11))),
% 0.50/0.67      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.50/0.67  thf('63', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (k1_zfmisc_1 @ 
% 0.50/0.67              (u1_struct_0 @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.50/0.67          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['61', '62'])).
% 0.50/0.67  thf('64', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.50/0.67          | ~ (l1_struct_0 @ X0)
% 0.50/0.67          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (k1_zfmisc_1 @ 
% 0.50/0.67              (u1_struct_0 @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['58', '63'])).
% 0.50/0.67  thf('65', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (k1_zfmisc_1 @ 
% 0.50/0.67              (u1_struct_0 @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.50/0.67          | ~ (l1_struct_0 @ X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['57', '64'])).
% 0.50/0.67  thf('66', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (l1_struct_0 @ X0)
% 0.50/0.67          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (k1_zfmisc_1 @ 
% 0.50/0.67              (u1_struct_0 @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0))),
% 0.50/0.67      inference('simplify', [status(thm)], ['65'])).
% 0.50/0.67  thf(t3_subset, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.67  thf('67', plain,
% 0.50/0.67      (![X5 : $i, X6 : $i]:
% 0.50/0.67         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.67  thf('68', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_struct_0 @ X0)
% 0.50/0.67          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (u1_struct_0 @ 
% 0.50/0.67              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['66', '67'])).
% 0.50/0.67  thf(d10_xboole_0, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.67  thf('69', plain,
% 0.50/0.67      (![X0 : $i, X2 : $i]:
% 0.50/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.67  thf('70', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (l1_struct_0 @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (r1_tarski @ 
% 0.50/0.67               (u1_struct_0 @ 
% 0.50/0.67                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.50/0.67               (u1_struct_0 @ X0))
% 0.50/0.67          | ((u1_struct_0 @ 
% 0.50/0.67              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.50/0.67              = (u1_struct_0 @ X0)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['68', '69'])).
% 0.50/0.67  thf('71', plain,
% 0.50/0.67      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.50/0.67        | ((u1_struct_0 @ 
% 0.50/0.67            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.50/0.67            = (u1_struct_0 @ sk_B))
% 0.50/0.67        | ~ (v2_pre_topc @ sk_B)
% 0.50/0.67        | ~ (l1_pre_topc @ sk_B)
% 0.50/0.67        | ~ (l1_struct_0 @ sk_B))),
% 0.50/0.67      inference('sup-', [status(thm)], ['56', '70'])).
% 0.50/0.67  thf('72', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('73', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('74', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf(dt_l1_pre_topc, axiom,
% 0.50/0.67    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.50/0.67  thf('76', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.50/0.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.50/0.67  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 0.50/0.67      inference('sup-', [status(thm)], ['75', '76'])).
% 0.50/0.67  thf('78', plain,
% 0.50/0.67      ((~ (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.50/0.67        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B)))),
% 0.50/0.67      inference('demod', [status(thm)], ['71', '72', '73', '74', '77'])).
% 0.50/0.67  thf('79', plain,
% 0.50/0.67      (![X13 : $i]:
% 0.50/0.67         ((v3_pre_topc @ (k2_struct_0 @ X13) @ X13)
% 0.50/0.67          | ~ (l1_pre_topc @ X13)
% 0.50/0.67          | ~ (v2_pre_topc @ X13))),
% 0.50/0.67      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.50/0.67  thf('80', plain,
% 0.50/0.67      (![X8 : $i]:
% 0.50/0.67         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.50/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.67  thf('81', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.50/0.67      inference('demod', [status(thm)], ['59', '60'])).
% 0.50/0.67  thf('82', plain,
% 0.50/0.67      (![X11 : $i, X12 : $i]:
% 0.50/0.67         (~ (v3_pre_topc @ X12 @ X11)
% 0.50/0.67          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.50/0.67          | (v3_pre_topc @ X12 @ 
% 0.50/0.67             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.50/0.67          | ~ (l1_pre_topc @ X11)
% 0.50/0.67          | ~ (v2_pre_topc @ X11))),
% 0.50/0.67      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.50/0.67  thf('83', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.50/0.67          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['81', '82'])).
% 0.50/0.67  thf('84', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.50/0.67          | ~ (l1_struct_0 @ X0)
% 0.50/0.67          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['80', '83'])).
% 0.50/0.67  thf('85', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.50/0.67          | ~ (l1_struct_0 @ X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['79', '84'])).
% 0.50/0.67  thf('86', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (l1_struct_0 @ X0)
% 0.50/0.67          | (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0))),
% 0.50/0.67      inference('simplify', [status(thm)], ['85'])).
% 0.50/0.67  thf('87', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (l1_struct_0 @ X0)
% 0.50/0.67          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (k1_zfmisc_1 @ 
% 0.50/0.67              (u1_struct_0 @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0))),
% 0.50/0.67      inference('simplify', [status(thm)], ['65'])).
% 0.50/0.67  thf('88', plain,
% 0.50/0.67      (![X10 : $i, X11 : $i]:
% 0.50/0.67         (~ (v3_pre_topc @ X10 @ 
% 0.50/0.67             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.50/0.67          | ~ (m1_subset_1 @ X10 @ 
% 0.50/0.67               (k1_zfmisc_1 @ 
% 0.50/0.67                (u1_struct_0 @ 
% 0.50/0.67                 (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))))
% 0.50/0.67          | (v3_pre_topc @ X10 @ X11)
% 0.50/0.67          | ~ (l1_pre_topc @ X11)
% 0.50/0.67          | ~ (v2_pre_topc @ X11))),
% 0.50/0.67      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.50/0.67  thf('89', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_struct_0 @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.50/0.67          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['87', '88'])).
% 0.50/0.67  thf('90', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.50/0.67             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.50/0.67          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.50/0.67          | ~ (l1_struct_0 @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0))),
% 0.50/0.67      inference('simplify', [status(thm)], ['89'])).
% 0.50/0.67  thf('91', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_struct_0 @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_struct_0 @ X0)
% 0.50/0.67          | (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['86', '90'])).
% 0.50/0.67  thf('92', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         ((v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.50/0.67          | ~ (l1_struct_0 @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | ~ (v2_pre_topc @ X0))),
% 0.50/0.67      inference('simplify', [status(thm)], ['91'])).
% 0.50/0.67  thf('93', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('94', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.50/0.67      inference('demod', [status(thm)], ['59', '60'])).
% 0.50/0.67  thf('95', plain,
% 0.50/0.67      (![X10 : $i, X11 : $i]:
% 0.50/0.67         (~ (v3_pre_topc @ X10 @ 
% 0.50/0.67             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.50/0.67          | ~ (m1_subset_1 @ X10 @ 
% 0.50/0.67               (k1_zfmisc_1 @ 
% 0.50/0.67                (u1_struct_0 @ 
% 0.50/0.67                 (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))))
% 0.50/0.67          | (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.50/0.67          | ~ (l1_pre_topc @ X11)
% 0.50/0.67          | ~ (v2_pre_topc @ X11))),
% 0.50/0.67      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.50/0.67  thf('96', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X0)
% 0.50/0.67          | ~ (l1_pre_topc @ X0)
% 0.50/0.67          | (m1_subset_1 @ 
% 0.50/0.67             (u1_struct_0 @ 
% 0.50/0.67              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.50/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.50/0.67          | ~ (v3_pre_topc @ 
% 0.50/0.67               (u1_struct_0 @ 
% 0.50/0.67                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))) @ 
% 0.50/0.67               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['94', '95'])).
% 0.50/0.67  thf('97', plain,
% 0.50/0.67      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ 
% 0.50/0.67           (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.50/0.67        | (m1_subset_1 @ 
% 0.50/0.67           (u1_struct_0 @ 
% 0.50/0.67            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))) @ 
% 0.50/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.50/0.67        | ~ (l1_pre_topc @ sk_B)
% 0.50/0.67        | ~ (v2_pre_topc @ sk_B))),
% 0.50/0.67      inference('sup-', [status(thm)], ['93', '96'])).
% 0.50/0.67  thf('98', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('99', plain,
% 0.50/0.67      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('101', plain, ((v2_pre_topc @ sk_B)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('102', plain,
% 0.50/0.67      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_C)
% 0.50/0.67        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.50/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.50/0.67      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 0.50/0.67  thf('103', plain,
% 0.50/0.67      ((~ (v2_pre_topc @ sk_C)
% 0.50/0.67        | ~ (l1_pre_topc @ sk_C)
% 0.50/0.67        | ~ (l1_struct_0 @ sk_C)
% 0.50/0.67        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.50/0.67           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['92', '102'])).
% 0.50/0.67  thf('104', plain, ((v2_pre_topc @ sk_C)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('105', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('106', plain, ((l1_pre_topc @ sk_C)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('107', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.50/0.67      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.50/0.67  thf('108', plain, ((l1_struct_0 @ sk_C)),
% 0.50/0.67      inference('sup-', [status(thm)], ['106', '107'])).
% 0.50/0.67  thf('109', plain,
% 0.50/0.67      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.50/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.50/0.67      inference('demod', [status(thm)], ['103', '104', '105', '108'])).
% 0.50/0.67  thf('110', plain,
% 0.50/0.67      (![X5 : $i, X6 : $i]:
% 0.50/0.67         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.50/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.67  thf('111', plain,
% 0.50/0.67      ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.50/0.67      inference('sup-', [status(thm)], ['109', '110'])).
% 0.50/0.67  thf('112', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['78', '111'])).
% 0.50/0.67  thf('113', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['5'])).
% 0.50/0.67  thf('114', plain,
% 0.50/0.67      (![X20 : $i, X21 : $i]:
% 0.50/0.67         (~ (m1_pre_topc @ X20 @ X21)
% 0.50/0.67          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.50/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.50/0.67          | ~ (l1_pre_topc @ X21))),
% 0.50/0.67      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.50/0.67  thf('115', plain,
% 0.50/0.67      (((~ (l1_pre_topc @ sk_A)
% 0.50/0.67         | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.50/0.67         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['113', '114'])).
% 0.50/0.67  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('117', plain,
% 0.50/0.67      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.50/0.67         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['115', '116'])).
% 0.50/0.67  thf('118', plain,
% 0.50/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.50/0.67         (~ (m1_pre_topc @ X17 @ X18)
% 0.50/0.67          | ((X19) != (u1_struct_0 @ X17))
% 0.50/0.67          | ~ (v3_pre_topc @ X19 @ X18)
% 0.50/0.67          | (v1_tsep_1 @ X17 @ X18)
% 0.50/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.50/0.67          | ~ (l1_pre_topc @ X18)
% 0.50/0.67          | ~ (v2_pre_topc @ X18))),
% 0.50/0.67      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.50/0.67  thf('119', plain,
% 0.50/0.67      (![X17 : $i, X18 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X18)
% 0.50/0.67          | ~ (l1_pre_topc @ X18)
% 0.50/0.67          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.50/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.50/0.67          | (v1_tsep_1 @ X17 @ X18)
% 0.50/0.67          | ~ (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.50/0.67          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.50/0.67      inference('simplify', [status(thm)], ['118'])).
% 0.50/0.67  thf('120', plain,
% 0.50/0.67      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.50/0.67         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.50/0.67         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.50/0.67         | ~ (l1_pre_topc @ sk_A)
% 0.50/0.67         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['117', '119'])).
% 0.50/0.67  thf('121', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['5'])).
% 0.50/0.67  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('124', plain,
% 0.50/0.67      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.50/0.67         | (v1_tsep_1 @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.50/0.67  thf('125', plain,
% 0.50/0.67      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.50/0.67         | (v1_tsep_1 @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['112', '124'])).
% 0.50/0.67  thf('126', plain,
% 0.50/0.67      (((v1_tsep_1 @ sk_B @ sk_A))
% 0.50/0.67         <= (((v1_tsep_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['55', '125'])).
% 0.50/0.67  thf('127', plain,
% 0.50/0.67      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['0'])).
% 0.50/0.67  thf('128', plain,
% 0.50/0.67      (((v1_tsep_1 @ sk_B @ sk_A)) | ~ ((v1_tsep_1 @ sk_C @ sk_A)) | 
% 0.50/0.67       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.50/0.67      inference('sup-', [status(thm)], ['126', '127'])).
% 0.50/0.67  thf('129', plain, (~ ((v1_tsep_1 @ sk_C @ sk_A))),
% 0.50/0.67      inference('sat_resolution*', [status(thm)], ['2', '4', '22', '40', '128'])).
% 0.50/0.67  thf('130', plain, (~ (v1_tsep_1 @ sk_C @ sk_A)),
% 0.50/0.67      inference('simpl_trail', [status(thm)], ['1', '129'])).
% 0.50/0.67  thf('131', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['23'])).
% 0.50/0.67  thf('132', plain,
% 0.50/0.67      (![X20 : $i, X21 : $i]:
% 0.50/0.67         (~ (m1_pre_topc @ X20 @ X21)
% 0.50/0.67          | (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.50/0.67             (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.50/0.67          | ~ (l1_pre_topc @ X21))),
% 0.50/0.67      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.50/0.67  thf('133', plain,
% 0.50/0.67      (((~ (l1_pre_topc @ sk_A)
% 0.50/0.67         | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.50/0.67            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.50/0.67         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['131', '132'])).
% 0.50/0.67  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('135', plain,
% 0.50/0.67      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.50/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.50/0.67         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['133', '134'])).
% 0.50/0.67  thf('136', plain,
% 0.50/0.67      (![X17 : $i, X18 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X18)
% 0.50/0.67          | ~ (l1_pre_topc @ X18)
% 0.50/0.67          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.50/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.50/0.67          | (v1_tsep_1 @ X17 @ X18)
% 0.50/0.67          | ~ (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.50/0.67          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.50/0.67      inference('simplify', [status(thm)], ['118'])).
% 0.50/0.67  thf('137', plain,
% 0.50/0.67      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.50/0.67         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.50/0.67         | (v1_tsep_1 @ sk_C @ sk_A)
% 0.50/0.67         | ~ (l1_pre_topc @ sk_A)
% 0.50/0.67         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['135', '136'])).
% 0.50/0.67  thf('138', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['23'])).
% 0.50/0.67  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('140', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('141', plain,
% 0.50/0.67      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.50/0.67         | (v1_tsep_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 0.50/0.67  thf('142', plain,
% 0.50/0.67      (![X8 : $i]:
% 0.50/0.67         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.50/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.67  thf('143', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['78', '111'])).
% 0.50/0.67  thf('144', plain,
% 0.50/0.67      ((((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_B))),
% 0.50/0.67      inference('sup+', [status(thm)], ['142', '143'])).
% 0.50/0.67  thf('145', plain, ((l1_struct_0 @ sk_B)),
% 0.50/0.67      inference('sup-', [status(thm)], ['75', '76'])).
% 0.50/0.67  thf('146', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['144', '145'])).
% 0.50/0.67  thf('147', plain,
% 0.50/0.67      (((~ (v3_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A)
% 0.50/0.67         | (v1_tsep_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['141', '146'])).
% 0.50/0.67  thf('148', plain, (((m1_pre_topc @ sk_C @ sk_A))),
% 0.50/0.67      inference('sat_resolution*', [status(thm)], ['4', '22'])).
% 0.50/0.67  thf('149', plain,
% 0.50/0.67      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A)
% 0.50/0.67        | (v1_tsep_1 @ sk_C @ sk_A))),
% 0.50/0.67      inference('simpl_trail', [status(thm)], ['147', '148'])).
% 0.50/0.67  thf('150', plain,
% 0.50/0.67      (![X8 : $i]:
% 0.50/0.67         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.50/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.50/0.67  thf('151', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['144', '145'])).
% 0.50/0.67  thf('152', plain,
% 0.50/0.67      ((((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_B)) | ~ (l1_struct_0 @ sk_C))),
% 0.50/0.67      inference('sup+', [status(thm)], ['150', '151'])).
% 0.50/0.67  thf('153', plain, ((l1_struct_0 @ sk_C)),
% 0.50/0.67      inference('sup-', [status(thm)], ['106', '107'])).
% 0.50/0.67  thf('154', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['152', '153'])).
% 0.50/0.67  thf('155', plain,
% 0.50/0.67      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['41'])).
% 0.50/0.67  thf('156', plain,
% 0.50/0.67      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.50/0.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.50/0.67         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['115', '116'])).
% 0.50/0.67  thf('157', plain,
% 0.50/0.67      (![X17 : $i, X18 : $i]:
% 0.50/0.67         (~ (v2_pre_topc @ X18)
% 0.50/0.67          | ~ (l1_pre_topc @ X18)
% 0.50/0.67          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.50/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.50/0.67          | (v3_pre_topc @ (u1_struct_0 @ X17) @ X18)
% 0.50/0.67          | ~ (v1_tsep_1 @ X17 @ X18)
% 0.50/0.67          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.50/0.67      inference('simplify', [status(thm)], ['48'])).
% 0.50/0.67  thf('158', plain,
% 0.50/0.67      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.50/0.67         | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.50/0.67         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.50/0.67         | ~ (l1_pre_topc @ sk_A)
% 0.50/0.67         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['156', '157'])).
% 0.50/0.67  thf('159', plain,
% 0.50/0.67      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['5'])).
% 0.50/0.67  thf('160', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('161', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('162', plain,
% 0.50/0.67      (((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.50/0.67         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)))
% 0.50/0.67         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['158', '159', '160', '161'])).
% 0.50/0.67  thf('163', plain,
% 0.50/0.67      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.50/0.67         <= (((v1_tsep_1 @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['155', '162'])).
% 0.50/0.67  thf('164', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['78', '111'])).
% 0.50/0.67  thf('165', plain, (((u1_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['144', '145'])).
% 0.50/0.67  thf('166', plain,
% 0.50/0.67      (((v3_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A))
% 0.50/0.67         <= (((v1_tsep_1 @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.50/0.67      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.50/0.67  thf('167', plain,
% 0.50/0.67      (((v1_tsep_1 @ sk_B @ sk_A)) | ((v1_tsep_1 @ sk_C @ sk_A))),
% 0.50/0.67      inference('split', [status(esa)], ['41'])).
% 0.50/0.67  thf('168', plain, (((v1_tsep_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('sat_resolution*', [status(thm)],
% 0.50/0.67                ['2', '4', '22', '40', '128', '167'])).
% 0.50/0.67  thf('169', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.50/0.67      inference('sat_resolution*', [status(thm)], ['4', '22', '40'])).
% 0.50/0.67  thf('170', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_B) @ sk_A)),
% 0.50/0.67      inference('simpl_trail', [status(thm)], ['166', '168', '169'])).
% 0.50/0.67  thf('171', plain, (((k2_struct_0 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.50/0.67      inference('demod', [status(thm)], ['152', '153'])).
% 0.50/0.67  thf('172', plain, ((v3_pre_topc @ (k2_struct_0 @ sk_C) @ sk_A)),
% 0.50/0.67      inference('demod', [status(thm)], ['170', '171'])).
% 0.50/0.67  thf('173', plain, ((v1_tsep_1 @ sk_C @ sk_A)),
% 0.50/0.67      inference('demod', [status(thm)], ['149', '154', '172'])).
% 0.50/0.67  thf('174', plain, ($false), inference('demod', [status(thm)], ['130', '173'])).
% 0.50/0.67  
% 0.50/0.67  % SZS output end Refutation
% 0.50/0.67  
% 0.50/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
