%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lUUn6A8Dok

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 (2189 expanded)
%              Number of leaves         :   22 ( 651 expanded)
%              Depth                    :   19
%              Number of atoms          : 1353 (37875 expanded)
%              Number of equality atoms :   61 (1824 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t13_tmap_1,conjecture,(
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
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( ( v1_borsuk_1 @ C @ A )
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
                 => ( ( ( v1_borsuk_1 @ B @ A )
                      & ( m1_pre_topc @ B @ A ) )
                  <=> ( ( v1_borsuk_1 @ C @ A )
                      & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_tmap_1])).

thf('0',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('5',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t11_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_borsuk_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( X9
       != ( u1_struct_0 @ X7 ) )
      | ~ ( v1_borsuk_1 @ X7 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X8 )
      | ( v4_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X7 ) @ X8 )
      | ~ ( v1_borsuk_1 @ X7 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('13',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( v1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('23',plain,
    ( ( v1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['20','26','27','28','29'])).

thf('31',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('32',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['20','26','27','28','29'])).

thf('39',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( sk_C
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_C != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ sk_B )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','40'])).

thf('42',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['42','43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ~ ( v1_borsuk_1 @ sk_B @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','45','46','47'])).

thf('49',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','48'])).

thf('50',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('53',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( X9
       != ( u1_struct_0 @ X7 ) )
      | ~ ( v4_pre_topc @ X9 @ X8 )
      | ( v1_borsuk_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_tsep_1])).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_borsuk_1 @ X7 @ X8 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X7 ) @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['50'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_borsuk_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','62'])).

thf('64',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( v1_borsuk_1 @ sk_C @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,
    ( ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('68',plain,
    ( ( v1_borsuk_1 @ sk_C @ sk_A )
   <= ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('70',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v4_pre_topc @ ( u1_struct_0 @ X7 ) @ X8 )
      | ~ ( v1_borsuk_1 @ X7 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('71',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['50'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ~ ( v1_borsuk_1 @ sk_C @ sk_A )
      | ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,
    ( ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('78',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_borsuk_1 @ X7 @ X8 )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X7 ) @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('79',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('81',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['42','43','44'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ~ ( v4_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_borsuk_1 @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ( ( v1_borsuk_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,
    ( ~ ( v1_borsuk_1 @ sk_B @ sk_A )
   <= ~ ( v1_borsuk_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('87',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
    | ~ ( v1_borsuk_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['50'])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['42','43','44'])).

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

thf('90',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ( X10
       != ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X12 )
      | ( m1_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('91',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( m1_pre_topc @ X11 @ X12 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) @ X12 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['20','26','27','28','29'])).

thf('94',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['42','43','44'])).

thf('96',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['42','43','44'])).

thf('99',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['20','26','27','28','29'])).

thf('100',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('101',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['42','43','44'])).

thf('103',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['20','26','27','28','29'])).

thf('104',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('105',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','96','97','98','99','100','101','102','103','104','105','106'])).

thf('108',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['88','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('112',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v1_borsuk_1 @ sk_B @ sk_A )
    | ( v1_borsuk_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('114',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['114'])).

thf('116',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('117',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['42','43','44'])).

thf('118',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ( X10
       != ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_pre_topc @ X10 @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('119',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['20','26','27','28','29'])).

thf('122',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('123',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['42','43','44'])).

thf('125',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['20','26','27','28','29'])).

thf('126',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('127',plain,(
    v2_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['42','43','44'])).

thf('129',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['20','26','27','28','29'])).

thf('130',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('131',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','125','126','127','128','129','130','131','132'])).

thf('134',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['116','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('138',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['66','67','87','112','113','115','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lUUn6A8Dok
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 134 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(t13_tmap_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.21/0.50               ( ( ( C ) =
% 0.21/0.50                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.21/0.50                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.50                   ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.21/0.50                  ( ( ( C ) =
% 0.21/0.50                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.21/0.50                    ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.50                      ( ( v1_borsuk_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t13_tmap_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((v1_borsuk_1 @ sk_C @ sk_A) | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (((v1_borsuk_1 @ sk_B @ sk_A)) <= (((v1_borsuk_1 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((v1_borsuk_1 @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf(t1_tsep_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.50           ( m1_subset_1 @
% 0.21/0.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.50          | (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.50          | ~ (l1_pre_topc @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.50         | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.50         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.50         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(t11_tsep_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                 ( ( ( v1_borsuk_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.21/0.50                   ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.50          | ((X9) != (u1_struct_0 @ X7))
% 0.21/0.50          | ~ (v1_borsuk_1 @ X7 @ X8)
% 0.21/0.50          | ~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.50          | (v4_pre_topc @ X9 @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | ~ (l1_pre_topc @ X8)
% 0.21/0.50          | ~ (v2_pre_topc @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (v2_pre_topc @ X8)
% 0.21/0.50          | ~ (l1_pre_topc @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | (v4_pre_topc @ (u1_struct_0 @ X7) @ X8)
% 0.21/0.50          | ~ (v1_borsuk_1 @ X7 @ X8)
% 0.21/0.50          | ~ (m1_pre_topc @ X7 @ X8))),
% 0.21/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.50         | ~ (v1_borsuk_1 @ sk_B @ sk_A)
% 0.21/0.50         | (v4_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.21/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf(abstractness_v1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ( v1_pre_topc @ A ) =>
% 0.21/0.50         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_pre_topc @ X0)
% 0.21/0.50          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_pre_topc @ X0)
% 0.21/0.50          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.21/0.50  thf(dt_u1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( m1_subset_1 @
% 0.21/0.50         ( u1_pre_topc @ A ) @ 
% 0.21/0.50         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X1 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.50          | ~ (l1_pre_topc @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.50  thf(free_g1_pre_topc, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50       ( ![C:$i,D:$i]:
% 0.21/0.50         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.21/0.50           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.21/0.50          | ((X6) = (X4))
% 0.21/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.50      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X0)
% 0.21/0.50          | ((u1_pre_topc @ X0) = (X1))
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.50              != (g1_pre_topc @ X2 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (v1_pre_topc @ X0)
% 0.21/0.50          | ((u1_pre_topc @ X0) = (X1))
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i]:
% 0.21/0.50         (((u1_pre_topc @ (g1_pre_topc @ X2 @ X1)) = (X1))
% 0.21/0.50          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.21/0.50          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((~ (v1_pre_topc @ sk_C)
% 0.21/0.50        | ~ (l1_pre_topc @ 
% 0.21/0.50             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.50        | ((u1_pre_topc @ 
% 0.21/0.50            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.50            = (u1_pre_topc @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(fc6_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ( v1_pre_topc @
% 0.21/0.50           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.21/0.50         ( v2_pre_topc @
% 0.21/0.50           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X2 : $i]:
% 0.21/0.50         ((v1_pre_topc @ 
% 0.21/0.50           (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.21/0.50          | ~ (l1_pre_topc @ X2)
% 0.21/0.50          | ~ (v2_pre_topc @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (((v1_pre_topc @ sk_C) | ~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain, ((v1_pre_topc @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '26', '27', '28', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X1 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.50          | ~ (l1_pre_topc @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.21/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.21/0.50          | ((X5) = (X3))
% 0.21/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.21/0.50      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((u1_struct_0 @ sk_B) = (X0))
% 0.21/0.50          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C))
% 0.21/0.50              != (g1_pre_topc @ X0 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '26', '27', '28', '29'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((u1_struct_0 @ sk_B) = (X0)) | ((sk_C) != (g1_pre_topc @ X0 @ X1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['36', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_C) != (X0))
% 0.21/0.50          | ~ (l1_pre_topc @ X0)
% 0.21/0.50          | ~ (v1_pre_topc @ X0)
% 0.21/0.50          | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))
% 0.21/0.50        | ~ (v1_pre_topc @ sk_C)
% 0.21/0.50        | ~ (l1_pre_topc @ sk_C))),
% 0.21/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.50  thf('43', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('44', plain, ((v1_pre_topc @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.50  thf('45', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (((~ (v1_borsuk_1 @ sk_B @ sk_A)
% 0.21/0.50         | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.21/0.50         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11', '45', '46', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.21/0.50         <= (((v1_borsuk_1 @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_C @ sk_A) | (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.50          | (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.50          | ~ (l1_pre_topc @ X14))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.50         | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.50            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.50         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.50  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.50         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X7 @ X8)
% 0.21/0.50          | ((X9) != (u1_struct_0 @ X7))
% 0.21/0.50          | ~ (v4_pre_topc @ X9 @ X8)
% 0.21/0.50          | (v1_borsuk_1 @ X7 @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | ~ (l1_pre_topc @ X8)
% 0.21/0.50          | ~ (v2_pre_topc @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t11_tsep_1])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (v2_pre_topc @ X8)
% 0.21/0.50          | ~ (l1_pre_topc @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | (v1_borsuk_1 @ X7 @ X8)
% 0.21/0.50          | ~ (v4_pre_topc @ (u1_struct_0 @ X7) @ X8)
% 0.21/0.50          | ~ (m1_pre_topc @ X7 @ X8))),
% 0.21/0.50      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.21/0.50         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.21/0.50         | (v1_borsuk_1 @ sk_C @ sk_A)
% 0.21/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['55', '57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['50'])).
% 0.21/0.50  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      (((~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.21/0.50         | (v1_borsuk_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (((v1_borsuk_1 @ sk_C @ sk_A))
% 0.21/0.50         <= (((v1_borsuk_1 @ sk_B @ sk_A)) & 
% 0.21/0.50             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.21/0.50             ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['49', '62'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.21/0.50        | ~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.21/0.50        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v1_borsuk_1 @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      ((~ (v1_borsuk_1 @ sk_C @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['64'])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (((v1_borsuk_1 @ sk_C @ sk_A)) | ~ ((v1_borsuk_1 @ sk_B @ sk_A)) | 
% 0.21/0.50       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['63', '65'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (~ ((v1_borsuk_1 @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A)) | 
% 0.21/0.50       ~ ((v1_borsuk_1 @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['64'])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (((v1_borsuk_1 @ sk_C @ sk_A)) <= (((v1_borsuk_1 @ sk_C @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.50         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (v2_pre_topc @ X8)
% 0.21/0.50          | ~ (l1_pre_topc @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | (v4_pre_topc @ (u1_struct_0 @ X7) @ X8)
% 0.21/0.50          | ~ (v1_borsuk_1 @ X7 @ X8)
% 0.21/0.50          | ~ (m1_pre_topc @ X7 @ X8))),
% 0.21/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.21/0.50         | ~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.21/0.50         | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.21/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['50'])).
% 0.21/0.50  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('75', plain,
% 0.21/0.50      (((~ (v1_borsuk_1 @ sk_C @ sk_A)
% 0.21/0.50         | (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.21/0.50         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      (((v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.21/0.50         <= (((v1_borsuk_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['68', '75'])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.50         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (v2_pre_topc @ X8)
% 0.21/0.50          | ~ (l1_pre_topc @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.50          | (v1_borsuk_1 @ X7 @ X8)
% 0.21/0.50          | ~ (v4_pre_topc @ (u1_struct_0 @ X7) @ X8)
% 0.21/0.50          | ~ (m1_pre_topc @ X7 @ X8))),
% 0.21/0.50      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.50         | ~ (v4_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.21/0.50         | (v1_borsuk_1 @ sk_B @ sk_A)
% 0.21/0.50         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.50  thf('80', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('81', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      (((~ (v4_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.21/0.50         | (v1_borsuk_1 @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.21/0.50  thf('85', plain,
% 0.21/0.50      (((v1_borsuk_1 @ sk_B @ sk_A))
% 0.21/0.50         <= (((v1_borsuk_1 @ sk_C @ sk_A)) & 
% 0.21/0.50             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.21/0.50             ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['76', '84'])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      ((~ (v1_borsuk_1 @ sk_B @ sk_A)) <= (~ ((v1_borsuk_1 @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['64'])).
% 0.21/0.50  thf('87', plain,
% 0.21/0.50      (((v1_borsuk_1 @ sk_B @ sk_A)) | ~ ((v1_borsuk_1 @ sk_C @ sk_A)) | 
% 0.21/0.50       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.50  thf('88', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['50'])).
% 0.21/0.50  thf('89', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf(t12_tmap_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.21/0.50               ( ( ( B ) =
% 0.21/0.50                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.21/0.50                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (v2_pre_topc @ X10)
% 0.21/0.50          | ~ (l1_pre_topc @ X10)
% 0.21/0.50          | ((X10) != (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.21/0.50          | ~ (m1_pre_topc @ X10 @ X12)
% 0.21/0.50          | (m1_pre_topc @ X11 @ X12)
% 0.21/0.50          | ~ (l1_pre_topc @ X11)
% 0.21/0.50          | ~ (v2_pre_topc @ X11)
% 0.21/0.50          | ~ (l1_pre_topc @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.21/0.50  thf('91', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X12)
% 0.21/0.50          | ~ (v2_pre_topc @ X11)
% 0.21/0.50          | ~ (l1_pre_topc @ X11)
% 0.21/0.50          | (m1_pre_topc @ X11 @ X12)
% 0.21/0.50          | ~ (m1_pre_topc @ 
% 0.21/0.50               (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)) @ X12)
% 0.21/0.50          | ~ (l1_pre_topc @ 
% 0.21/0.50               (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.21/0.50          | ~ (v2_pre_topc @ 
% 0.21/0.50               (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['90'])).
% 0.21/0.50  thf('92', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ 
% 0.21/0.50             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))
% 0.21/0.50          | ~ (v2_pre_topc @ 
% 0.21/0.50               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.50          | ~ (m1_pre_topc @ 
% 0.21/0.50               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.21/0.50          | (m1_pre_topc @ sk_B @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['89', '91'])).
% 0.21/0.50  thf('93', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '26', '27', '28', '29'])).
% 0.21/0.50  thf('94', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('95', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('96', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.50  thf('97', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('98', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('99', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '26', '27', '28', '29'])).
% 0.21/0.50  thf('100', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.50  thf('101', plain, ((v2_pre_topc @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('102', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('103', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '26', '27', '28', '29'])).
% 0.21/0.50  thf('104', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.50  thf('105', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('106', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('107', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.50          | (m1_pre_topc @ sk_B @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['92', '93', '96', '97', '98', '99', '100', '101', '102', 
% 0.21/0.50                 '103', '104', '105', '106'])).
% 0.21/0.50  thf('108', plain,
% 0.21/0.50      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A)))
% 0.21/0.50         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['88', '107'])).
% 0.21/0.50  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('110', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['108', '109'])).
% 0.21/0.50  thf('111', plain,
% 0.21/0.50      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['64'])).
% 0.21/0.50  thf('112', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['110', '111'])).
% 0.21/0.50  thf('113', plain,
% 0.21/0.50      (((v1_borsuk_1 @ sk_B @ sk_A)) | ((v1_borsuk_1 @ sk_C @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('114', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('115', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_B @ sk_A)) | ((m1_pre_topc @ sk_C @ sk_A))),
% 0.21/0.50      inference('split', [status(esa)], ['114'])).
% 0.21/0.50  thf('116', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('117', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('118', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (v2_pre_topc @ X10)
% 0.21/0.50          | ~ (l1_pre_topc @ X10)
% 0.21/0.50          | ((X10) != (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.21/0.50          | ~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.50          | (m1_pre_topc @ X10 @ X12)
% 0.21/0.50          | ~ (l1_pre_topc @ X11)
% 0.21/0.50          | ~ (v2_pre_topc @ X11)
% 0.21/0.50          | ~ (l1_pre_topc @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.21/0.50  thf('119', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ X12)
% 0.21/0.50          | ~ (v2_pre_topc @ X11)
% 0.21/0.50          | ~ (l1_pre_topc @ X11)
% 0.21/0.50          | (m1_pre_topc @ 
% 0.21/0.50             (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)) @ X12)
% 0.21/0.50          | ~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.50          | ~ (l1_pre_topc @ 
% 0.21/0.50               (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.21/0.50          | ~ (v2_pre_topc @ 
% 0.21/0.50               (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['118'])).
% 0.21/0.50  thf('120', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ 
% 0.21/0.50             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))
% 0.21/0.50          | ~ (v2_pre_topc @ 
% 0.21/0.50               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.21/0.50          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.50          | (m1_pre_topc @ 
% 0.21/0.50             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['117', '119'])).
% 0.21/0.50  thf('121', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '26', '27', '28', '29'])).
% 0.21/0.50  thf('122', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.50  thf('123', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('124', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('125', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '26', '27', '28', '29'])).
% 0.21/0.50  thf('126', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.50  thf('127', plain, ((v2_pre_topc @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('128', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['42', '43', '44'])).
% 0.21/0.50  thf('129', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '26', '27', '28', '29'])).
% 0.21/0.50  thf('130', plain,
% 0.21/0.50      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.50  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('132', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('133', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.50          | (m1_pre_topc @ sk_C @ X0)
% 0.21/0.50          | ~ (l1_pre_topc @ X0))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['120', '121', '122', '123', '124', '125', '126', '127', 
% 0.21/0.50                 '128', '129', '130', '131', '132'])).
% 0.21/0.50  thf('134', plain,
% 0.21/0.50      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_C @ sk_A)))
% 0.21/0.50         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['116', '133'])).
% 0.21/0.50  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('136', plain,
% 0.21/0.50      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['134', '135'])).
% 0.21/0.50  thf('137', plain,
% 0.21/0.50      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['64'])).
% 0.21/0.50  thf('138', plain,
% 0.21/0.50      (~ ((m1_pre_topc @ sk_B @ sk_A)) | ((m1_pre_topc @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['136', '137'])).
% 0.21/0.50  thf('139', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)],
% 0.21/0.50                ['66', '67', '87', '112', '113', '115', '138'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
