%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ih3tBNVfe3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:08 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  169 (2213 expanded)
%              Number of leaves         :   22 ( 657 expanded)
%              Depth                    :   19
%              Number of atoms          : 1608 (38375 expanded)
%              Number of equality atoms :   72 (1844 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('8',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( u1_struct_0 @ X11 ) )
      | ~ ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v3_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v1_tsep_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('16',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
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

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ~ ( v1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('26',plain,
    ( ( v1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['23','29','30','31','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('35',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['23','29','30','31','32'])).

thf('42',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( sk_C
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_C != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ sk_B )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','43'])).

thf('45',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['45','46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','48','49','50'])).

thf('52',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','51'])).

thf('53',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('56',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( u1_struct_0 @ X11 ) )
      | ~ ( v3_pre_topc @ X13 @ X12 )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
   <= ( ( v1_tsep_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('68',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['45','46','47'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf(t31_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( l1_pre_topc @ C )
             => ! [D: $i] :
                  ( ( l1_pre_topc @ D )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) )
                      & ( m1_pre_topc @ C @ A ) )
                   => ( m1_pre_topc @ D @ B ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( m1_pre_topc @ X8 @ X7 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( m1_pre_topc @ X0 @ X3 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) @ X3 )
      | ~ ( m1_pre_topc @ X1 @ X2 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(eq_res,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['23','29','30','31','32'])).

thf('79',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('80',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['45','46','47'])).

thf('81',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('83',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['45','46','47'])).

thf('84',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['23','29','30','31','32'])).

thf('85',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('86',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['45','46','47'])).

thf('89',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['23','29','30','31','32'])).

thf('90',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','81','82','83','84','85','86','87','88','89','90'])).

thf('92',plain,
    ( ( ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('96',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
   <= ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('99',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('100',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v1_tsep_1 @ sk_C @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('107',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v1_tsep_1 @ X11 @ X12 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('108',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('110',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['45','46','47'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( ( v1_tsep_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','113'])).

thf('115',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('116',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['117'])).

thf('119',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('120',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['45','46','47'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('122',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 )
      | ( m1_pre_topc @ X8 @ X7 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( m1_pre_topc @ X9 @ X10 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X10 ) @ ( u1_pre_topc @ X10 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t31_pre_topc])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ( m1_pre_topc @ X1 @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_pre_topc @ X1 @ X3 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) @ X2 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X1 ) @ ( u1_pre_topc @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(eq_res,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['23','29','30','31','32'])).

thf('129',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('130',plain,(
    v1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('131',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['45','46','47'])).

thf('132',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['23','29','30','31','32'])).

thf('133',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('134',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['45','46','47'])).

thf('136',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['23','29','30','31','32'])).

thf('137',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('138',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131','132','133','134','135','136','137','138'])).

thf('140',plain,
    ( ( ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['119','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('144',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','68','96','116','118','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ih3tBNVfe3
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:12:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 192 iterations in 0.119s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.39/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.58  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(t14_tmap_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.39/0.58               ( ( ( C ) =
% 0.39/0.58                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.39/0.58                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.39/0.58                   ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.39/0.58              ( ![C:$i]:
% 0.39/0.58                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.39/0.58                  ( ( ( C ) =
% 0.39/0.58                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.39/0.58                    ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.39/0.58                      ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t14_tmap_1])).
% 0.39/0.58  thf('0', plain, (((v1_tsep_1 @ sk_C @ sk_A) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain, (((v1_tsep_1 @ sk_C @ sk_A)) | ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.39/0.58        | ~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.39/0.58        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.39/0.58        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (~ ((v1_tsep_1 @ sk_C @ sk_A)) | ~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.39/0.58       ~ ((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('5', plain, (((v1_tsep_1 @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['5'])).
% 0.39/0.58  thf(t1_tsep_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.58           ( m1_subset_1 @
% 0.39/0.58             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X14 : $i, X15 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X14 @ X15)
% 0.39/0.58          | (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.39/0.58          | ~ (l1_pre_topc @ X15))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.58         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf(t16_tsep_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.58               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.39/0.58                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.39/0.58                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X11 @ X12)
% 0.39/0.58          | ((X13) != (u1_struct_0 @ X11))
% 0.39/0.58          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.39/0.58          | ~ (m1_pre_topc @ X11 @ X12)
% 0.39/0.58          | (v3_pre_topc @ X13 @ X12)
% 0.39/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.58          | ~ (l1_pre_topc @ X12)
% 0.39/0.58          | ~ (v2_pre_topc @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         (~ (v2_pre_topc @ X12)
% 0.39/0.58          | ~ (l1_pre_topc @ X12)
% 0.39/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.39/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.58          | (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.39/0.58          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.39/0.58          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.39/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.39/0.58         | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.39/0.58         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.39/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['10', '12'])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['5'])).
% 0.39/0.58  thf(abstractness_v1_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ( v1_pre_topc @ A ) =>
% 0.39/0.58         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_pre_topc @ X0)
% 0.39/0.58          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_pre_topc @ X0)
% 0.39/0.58          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.39/0.58  thf(dt_u1_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( m1_subset_1 @
% 0.39/0.58         ( u1_pre_topc @ A ) @ 
% 0.39/0.58         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X1 : $i]:
% 0.39/0.58         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.39/0.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.39/0.58          | ~ (l1_pre_topc @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.39/0.58  thf(free_g1_pre_topc, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.58       ( ![C:$i,D:$i]:
% 0.39/0.58         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.39/0.58           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.58         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.39/0.58          | ((X6) = (X4))
% 0.39/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.39/0.58      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | ((u1_pre_topc @ X0) = (X1))
% 0.39/0.58          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.39/0.58              != (g1_pre_topc @ X2 @ X1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_pre_topc @ X0)
% 0.39/0.58          | ((u1_pre_topc @ X0) = (X1))
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X1 : $i, X2 : $i]:
% 0.39/0.58         (((u1_pre_topc @ (g1_pre_topc @ X2 @ X1)) = (X1))
% 0.39/0.58          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.39/0.58          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      ((~ (v1_pre_topc @ sk_C)
% 0.39/0.58        | ~ (l1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.39/0.58        | ((u1_pre_topc @ 
% 0.39/0.58            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.39/0.58            = (u1_pre_topc @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(fc6_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ( v1_pre_topc @
% 0.39/0.58           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.39/0.58         ( v2_pre_topc @
% 0.39/0.58           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X2 : $i]:
% 0.39/0.58         ((v1_pre_topc @ 
% 0.39/0.58           (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.39/0.58          | ~ (l1_pre_topc @ X2)
% 0.39/0.58          | ~ (v2_pre_topc @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (((v1_pre_topc @ sk_C) | ~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('28', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('29', plain, ((v1_pre_topc @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('31', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('33', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '29', '30', '31', '32'])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X1 : $i]:
% 0.39/0.58         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.39/0.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.39/0.58          | ~ (l1_pre_topc @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.39/0.58        | ~ (l1_pre_topc @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      ((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.58         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.39/0.58          | ((X5) = (X3))
% 0.39/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.39/0.58      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((u1_struct_0 @ sk_B) = (X0))
% 0.39/0.58          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C))
% 0.39/0.58              != (g1_pre_topc @ X0 @ X1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('41', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '29', '30', '31', '32'])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((u1_struct_0 @ sk_B) = (X0)) | ((sk_C) != (g1_pre_topc @ X0 @ X1)))),
% 0.39/0.58      inference('demod', [status(thm)], ['39', '42'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((sk_C) != (X0))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_pre_topc @ X0)
% 0.39/0.58          | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['15', '43'])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      ((((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))
% 0.39/0.58        | ~ (v1_pre_topc @ sk_C)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_C))),
% 0.39/0.58      inference('simplify', [status(thm)], ['44'])).
% 0.39/0.58  thf('46', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('47', plain, ((v1_pre_topc @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.39/0.58  thf('48', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('simplify_reflect+', [status(thm)], ['45', '46', '47'])).
% 0.39/0.58  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.39/0.58         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.39/0.58         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['13', '14', '48', '49', '50'])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.39/0.58         <= (((v1_tsep_1 @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['4', '51'])).
% 0.39/0.58  thf('53', plain, (((m1_pre_topc @ sk_C @ sk_A) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['53'])).
% 0.39/0.58  thf('55', plain,
% 0.39/0.58      (![X14 : $i, X15 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X14 @ X15)
% 0.39/0.58          | (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.39/0.58          | ~ (l1_pre_topc @ X15))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.58  thf('56', plain,
% 0.39/0.58      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.58            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.58         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['54', '55'])).
% 0.39/0.58  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('58', plain,
% 0.39/0.58      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.39/0.58  thf('59', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X11 @ X12)
% 0.39/0.58          | ((X13) != (u1_struct_0 @ X11))
% 0.39/0.58          | ~ (v3_pre_topc @ X13 @ X12)
% 0.39/0.58          | (v1_tsep_1 @ X11 @ X12)
% 0.39/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.58          | ~ (l1_pre_topc @ X12)
% 0.39/0.58          | ~ (v2_pre_topc @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.39/0.58  thf('60', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         (~ (v2_pre_topc @ X12)
% 0.39/0.58          | ~ (l1_pre_topc @ X12)
% 0.39/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.39/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.58          | (v1_tsep_1 @ X11 @ X12)
% 0.39/0.58          | ~ (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.39/0.58          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.39/0.58      inference('simplify', [status(thm)], ['59'])).
% 0.39/0.58  thf('61', plain,
% 0.39/0.58      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.39/0.58         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.39/0.58         | (v1_tsep_1 @ sk_C @ sk_A)
% 0.39/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['58', '60'])).
% 0.39/0.58  thf('62', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['53'])).
% 0.39/0.58  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('65', plain,
% 0.39/0.58      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.39/0.58         | (v1_tsep_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.39/0.58  thf('66', plain,
% 0.39/0.58      (((v1_tsep_1 @ sk_C @ sk_A))
% 0.39/0.58         <= (((v1_tsep_1 @ sk_B @ sk_A)) & 
% 0.39/0.58             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.39/0.58             ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['52', '65'])).
% 0.39/0.58  thf('67', plain,
% 0.39/0.58      ((~ (v1_tsep_1 @ sk_C @ sk_A)) <= (~ ((v1_tsep_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('68', plain,
% 0.39/0.58      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A)) | 
% 0.39/0.58       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ((v1_tsep_1 @ sk_C @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.39/0.58  thf('69', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['5'])).
% 0.39/0.58  thf('70', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('simplify_reflect+', [status(thm)], ['45', '46', '47'])).
% 0.39/0.58  thf('71', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_pre_topc @ X0)
% 0.39/0.58          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.39/0.58  thf(t31_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( l1_pre_topc @ B ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( l1_pre_topc @ C ) =>
% 0.39/0.58               ( ![D:$i]:
% 0.39/0.58                 ( ( l1_pre_topc @ D ) =>
% 0.39/0.58                   ( ( ( ( g1_pre_topc @
% 0.39/0.58                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.39/0.58                         ( g1_pre_topc @
% 0.39/0.58                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.39/0.58                       ( ( g1_pre_topc @
% 0.39/0.58                           ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.39/0.58                         ( g1_pre_topc @
% 0.39/0.58                           ( u1_struct_0 @ D ) @ ( u1_pre_topc @ D ) ) ) & 
% 0.39/0.58                       ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.58                     ( m1_pre_topc @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('72', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X7)
% 0.39/0.58          | ~ (l1_pre_topc @ X8)
% 0.39/0.58          | (m1_pre_topc @ X8 @ X7)
% 0.39/0.58          | ((g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))
% 0.39/0.58              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.39/0.58          | ~ (m1_pre_topc @ X9 @ X10)
% 0.39/0.58          | ((g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))
% 0.39/0.58              != (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.39/0.58          | ~ (l1_pre_topc @ X9)
% 0.39/0.58          | ~ (l1_pre_topc @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.39/0.58  thf('73', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (((g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) != (X0))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X2)
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.39/0.58              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.39/0.58          | ~ (m1_pre_topc @ X1 @ X2)
% 0.39/0.58          | (m1_pre_topc @ X0 @ X3)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X3))),
% 0.39/0.58      inference('sup-', [status(thm)], ['71', '72'])).
% 0.39/0.58  thf('74', plain,
% 0.39/0.58      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X3)
% 0.39/0.58          | (m1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X3)
% 0.39/0.58          | ~ (m1_pre_topc @ X1 @ X2)
% 0.39/0.58          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.39/0.58              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | ~ (l1_pre_topc @ X2)
% 0.39/0.58          | ~ (v1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.39/0.58          | ~ (l1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['73'])).
% 0.39/0.58  thf('75', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.58          | ~ (v1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.58          | (m1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.39/0.58          | ~ (l1_pre_topc @ X1))),
% 0.39/0.58      inference('eq_res', [status(thm)], ['74'])).
% 0.39/0.58  thf('76', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((m1_pre_topc @ 
% 0.39/0.58           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.39/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | ~ (v1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.58          | ~ (l1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['75'])).
% 0.39/0.58  thf('77', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))
% 0.39/0.58          | ~ (l1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.58          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.39/0.58          | (m1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['70', '76'])).
% 0.39/0.58  thf('78', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '29', '30', '31', '32'])).
% 0.39/0.58  thf('79', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.39/0.58  thf('80', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('simplify_reflect+', [status(thm)], ['45', '46', '47'])).
% 0.39/0.58  thf('81', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['79', '80'])).
% 0.39/0.58  thf('82', plain, ((v1_pre_topc @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.39/0.58  thf('83', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('simplify_reflect+', [status(thm)], ['45', '46', '47'])).
% 0.39/0.58  thf('84', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '29', '30', '31', '32'])).
% 0.39/0.58  thf('85', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['79', '80'])).
% 0.39/0.58  thf('86', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('88', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('simplify_reflect+', [status(thm)], ['45', '46', '47'])).
% 0.39/0.58  thf('89', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '29', '30', '31', '32'])).
% 0.39/0.58  thf('90', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['79', '80'])).
% 0.39/0.58  thf('91', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.39/0.58          | (m1_pre_topc @ sk_C @ X0))),
% 0.39/0.58      inference('demod', [status(thm)],
% 0.39/0.58                ['77', '78', '81', '82', '83', '84', '85', '86', '87', '88', 
% 0.39/0.58                 '89', '90'])).
% 0.39/0.58  thf('92', plain,
% 0.39/0.58      ((((m1_pre_topc @ sk_C @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.39/0.58         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['69', '91'])).
% 0.39/0.58  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('94', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['92', '93'])).
% 0.39/0.58  thf('95', plain,
% 0.39/0.58      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('96', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['94', '95'])).
% 0.39/0.58  thf('97', plain,
% 0.39/0.58      (((v1_tsep_1 @ sk_C @ sk_A)) <= (((v1_tsep_1 @ sk_C @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['0'])).
% 0.39/0.58  thf('98', plain,
% 0.39/0.58      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.39/0.58  thf('99', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         (~ (v2_pre_topc @ X12)
% 0.39/0.58          | ~ (l1_pre_topc @ X12)
% 0.39/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.39/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.58          | (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.39/0.58          | ~ (v1_tsep_1 @ X11 @ X12)
% 0.39/0.58          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.39/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.58  thf('100', plain,
% 0.39/0.58      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.39/0.58         | ~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.39/0.58         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.39/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['98', '99'])).
% 0.39/0.58  thf('101', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['53'])).
% 0.39/0.58  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('103', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('104', plain,
% 0.39/0.58      (((~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.39/0.58         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.39/0.58         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.39/0.58  thf('105', plain,
% 0.39/0.58      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.39/0.58         <= (((v1_tsep_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['97', '104'])).
% 0.39/0.58  thf('106', plain,
% 0.39/0.58      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.58         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('107', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         (~ (v2_pre_topc @ X12)
% 0.39/0.58          | ~ (l1_pre_topc @ X12)
% 0.39/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.39/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.39/0.58          | (v1_tsep_1 @ X11 @ X12)
% 0.39/0.58          | ~ (v3_pre_topc @ (u1_struct_0 @ X11) @ X12)
% 0.39/0.58          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.39/0.58      inference('simplify', [status(thm)], ['59'])).
% 0.39/0.58  thf('108', plain,
% 0.39/0.58      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.39/0.58         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.39/0.58         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.39/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.58         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['106', '107'])).
% 0.39/0.58  thf('109', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['5'])).
% 0.39/0.58  thf('110', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('simplify_reflect+', [status(thm)], ['45', '46', '47'])).
% 0.39/0.58  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('113', plain,
% 0.39/0.58      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.39/0.58         | (v1_tsep_1 @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.39/0.58  thf('114', plain,
% 0.39/0.58      (((v1_tsep_1 @ sk_B @ sk_A))
% 0.39/0.58         <= (((v1_tsep_1 @ sk_C @ sk_A)) & 
% 0.39/0.58             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.39/0.58             ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['105', '113'])).
% 0.39/0.58  thf('115', plain,
% 0.39/0.58      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('116', plain,
% 0.39/0.58      (~ ((v1_tsep_1 @ sk_C @ sk_A)) | ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.39/0.58       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['114', '115'])).
% 0.39/0.58  thf('117', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('118', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('split', [status(esa)], ['117'])).
% 0.39/0.58  thf('119', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['53'])).
% 0.39/0.58  thf('120', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('simplify_reflect+', [status(thm)], ['45', '46', '47'])).
% 0.39/0.58  thf('121', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_pre_topc @ X0)
% 0.39/0.58          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.39/0.58  thf('122', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X7)
% 0.39/0.58          | ~ (l1_pre_topc @ X8)
% 0.39/0.58          | (m1_pre_topc @ X8 @ X7)
% 0.39/0.58          | ((g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))
% 0.39/0.58              != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.39/0.58          | ~ (m1_pre_topc @ X9 @ X10)
% 0.39/0.58          | ((g1_pre_topc @ (u1_struct_0 @ X10) @ (u1_pre_topc @ X10))
% 0.39/0.58              != (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.39/0.58          | ~ (l1_pre_topc @ X9)
% 0.39/0.58          | ~ (l1_pre_topc @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t31_pre_topc])).
% 0.39/0.58  thf('123', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (((X0) != (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (v1_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X2)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.39/0.58              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.39/0.58          | ~ (m1_pre_topc @ X0 @ X2)
% 0.39/0.58          | (m1_pre_topc @ X1 @ X3)
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | ~ (l1_pre_topc @ X3))),
% 0.39/0.58      inference('sup-', [status(thm)], ['121', '122'])).
% 0.39/0.58  thf('124', plain,
% 0.39/0.58      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X3)
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | (m1_pre_topc @ X1 @ X3)
% 0.39/0.58          | ~ (m1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)) @ X2)
% 0.39/0.58          | ((g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2))
% 0.39/0.58              != (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.39/0.58          | ~ (l1_pre_topc @ X2)
% 0.39/0.58          | ~ (v1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1)))
% 0.39/0.58          | ~ (l1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X1) @ (u1_pre_topc @ X1))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['123'])).
% 0.39/0.58  thf('125', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.58          | ~ (v1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | ~ (m1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.39/0.58          | (m1_pre_topc @ X0 @ X1)
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ X1))),
% 0.39/0.58      inference('eq_res', [status(thm)], ['124'])).
% 0.39/0.58  thf('126', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | (m1_pre_topc @ X0 @ X1)
% 0.39/0.58          | ~ (m1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X1)
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | ~ (v1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.39/0.58          | ~ (l1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['125'])).
% 0.39/0.58  thf('127', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))
% 0.39/0.58          | ~ (l1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.39/0.58          | ~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (m1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.39/0.58          | (m1_pre_topc @ sk_B @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['120', '126'])).
% 0.39/0.58  thf('128', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '29', '30', '31', '32'])).
% 0.39/0.58  thf('129', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['79', '80'])).
% 0.39/0.58  thf('130', plain, ((v1_pre_topc @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.39/0.58  thf('131', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('simplify_reflect+', [status(thm)], ['45', '46', '47'])).
% 0.39/0.58  thf('132', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '29', '30', '31', '32'])).
% 0.39/0.58  thf('133', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['79', '80'])).
% 0.39/0.58  thf('134', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('135', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.58      inference('simplify_reflect+', [status(thm)], ['45', '46', '47'])).
% 0.39/0.58  thf('136', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['23', '29', '30', '31', '32'])).
% 0.39/0.58  thf('137', plain,
% 0.39/0.58      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['79', '80'])).
% 0.39/0.58  thf('138', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('139', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X0)
% 0.39/0.58          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.39/0.58          | (m1_pre_topc @ sk_B @ X0))),
% 0.39/0.58      inference('demod', [status(thm)],
% 0.39/0.58                ['127', '128', '129', '130', '131', '132', '133', '134', 
% 0.39/0.58                 '135', '136', '137', '138'])).
% 0.39/0.58  thf('140', plain,
% 0.39/0.58      ((((m1_pre_topc @ sk_B @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.39/0.58         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['119', '139'])).
% 0.39/0.58  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('142', plain,
% 0.39/0.58      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['140', '141'])).
% 0.39/0.58  thf('143', plain,
% 0.39/0.58      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.39/0.58      inference('split', [status(esa)], ['2'])).
% 0.39/0.58  thf('144', plain,
% 0.39/0.58      (~ ((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['142', '143'])).
% 0.39/0.58  thf('145', plain, ($false),
% 0.39/0.58      inference('sat_resolution*', [status(thm)],
% 0.39/0.58                ['1', '3', '68', '96', '116', '118', '144'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.43/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
