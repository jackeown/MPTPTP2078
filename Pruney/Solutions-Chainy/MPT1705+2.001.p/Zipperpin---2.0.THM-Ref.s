%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jbqXklon2w

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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
   <= ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
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
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( X12
       != ( u1_struct_0 @ X10 ) )
      | ~ ( v1_tsep_1 @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X11 )
      | ( v3_pre_topc @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X10 ) @ X11 )
      | ~ ( v1_tsep_1 @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v1_tsep_1 @ sk_C @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('19',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( X12
       != ( u1_struct_0 @ X10 ) )
      | ~ ( v3_pre_topc @ X12 @ X11 )
      | ( v1_tsep_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_tsep_1 @ X10 @ X11 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X10 ) @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('27',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
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

thf('29',plain,(
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

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      = ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('37',plain,
    ( ( v1_pre_topc @ sk_C )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['34','40','41','42','43'])).

thf('45',plain,(
    ! [X1: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('46',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['34','40','41','42','43'])).

thf('53',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( sk_C
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_C != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ sk_B )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','54'])).

thf('56',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) )
    | ~ ( v1_pre_topc @ sk_C )
    | ~ ( l1_pre_topc @ sk_C ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    l1_pre_topc @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['56','57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','59','60','61'])).

thf('63',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( ( v1_tsep_1 @ sk_C @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','62'])).

thf('64',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X10 ) @ X11 )
      | ~ ( v1_tsep_1 @ X10 @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('70',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ~ ( v1_tsep_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('72',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['56','57','58'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
   <= ( ( v1_tsep_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','75'])).

thf('77',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v1_tsep_1 @ X10 @ X11 )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X10 ) @ X11 )
      | ~ ( m1_pre_topc @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('79',plain,
    ( ( ~ ( m1_pre_topc @ sk_C @ sk_A )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_C ) @ sk_A )
      | ( v1_tsep_1 @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
   <= ( ( v1_tsep_1 @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_B @ sk_A )
      & ( m1_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('86',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( v1_tsep_1 @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('88',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['16'])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['56','57','58'])).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( X7
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( m1_pre_topc @ X7 @ X9 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('91',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) @ X9 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['34','40','41','42','43'])).

thf('94',plain,
    ( sk_C
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['56','57','58'])).

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
    inference('simplify_reflect+',[status(thm)],['56','57','58'])).

thf('99',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['34','40','41','42','43'])).

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
    inference('simplify_reflect+',[status(thm)],['56','57','58'])).

thf('103',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['34','40','41','42','43'])).

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
      ( ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93','96','97','98','99','100','101','102','103','104','105','106'])).

thf('108',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
   <= ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('112',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('114',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['114'])).

thf('116',plain,
    ( ( m1_pre_topc @ sk_C @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('117',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference('simplify_reflect+',[status(thm)],['56','57','58'])).

thf('118',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( X7
       != ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( m1_pre_topc @ X7 @ X9 )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('119',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ( m1_pre_topc @ X8 @ X9 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) @ X9 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['34','40','41','42','43'])).

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
    inference('simplify_reflect+',[status(thm)],['56','57','58'])).

thf('125',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['34','40','41','42','43'])).

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
    inference('simplify_reflect+',[status(thm)],['56','57','58'])).

thf('129',plain,
    ( ( u1_pre_topc @ sk_C )
    = ( u1_pre_topc @ sk_B ) ),
    inference(demod,[status(thm)],['34','40','41','42','43'])).

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
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124','125','126','127','128','129','130','131','132'])).

thf('134',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['116','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( m1_pre_topc @ sk_B @ sk_A )
   <= ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('138',plain,
    ( ~ ( m1_pre_topc @ sk_C @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['66','86','87','112','113','115','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jbqXklon2w
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 129 iterations in 0.050s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(t14_tmap_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.20/0.48               ( ( ( C ) =
% 0.20/0.48                   ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.20/0.48                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.48                   ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.20/0.48                  ( ( ( C ) =
% 0.20/0.48                      ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.20/0.48                    ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.48                      ( ( v1_tsep_1 @ C @ A ) & ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t14_tmap_1])).
% 0.20/0.48  thf('0', plain, (((v1_tsep_1 @ sk_C @ sk_A) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (((v1_tsep_1 @ sk_C @ sk_A)) <= (((v1_tsep_1 @ sk_C @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain, (((m1_pre_topc @ sk_C @ sk_A) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf(t1_tsep_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( m1_subset_1 @
% 0.20/0.48             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.48          | (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.48          | ~ (l1_pre_topc @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.48            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.48         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(t16_tsep_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.48                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.20/0.48                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.48          | ((X12) != (u1_struct_0 @ X10))
% 0.20/0.48          | ~ (v1_tsep_1 @ X10 @ X11)
% 0.20/0.48          | ~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.48          | (v3_pre_topc @ X12 @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.48          | ~ (l1_pre_topc @ X11)
% 0.20/0.48          | ~ (v2_pre_topc @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (v2_pre_topc @ X11)
% 0.20/0.48          | ~ (l1_pre_topc @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.48          | (v3_pre_topc @ (u1_struct_0 @ X10) @ X11)
% 0.20/0.48          | ~ (v1_tsep_1 @ X10 @ X11)
% 0.20/0.48          | ~ (m1_pre_topc @ X10 @ X11))),
% 0.20/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.48         | ~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.20/0.48         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.20/0.48         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (((~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.20/0.48         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.20/0.48         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.20/0.48         <= (((v1_tsep_1 @ sk_C @ sk_A)) & ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '14'])).
% 0.20/0.48  thf('16', plain, (((v1_tsep_1 @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.48          | (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.48          | ~ (l1_pre_topc @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.48         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ X10 @ X11)
% 0.20/0.48          | ((X12) != (u1_struct_0 @ X10))
% 0.20/0.48          | ~ (v3_pre_topc @ X12 @ X11)
% 0.20/0.48          | (v1_tsep_1 @ X10 @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.48          | ~ (l1_pre_topc @ X11)
% 0.20/0.48          | ~ (v2_pre_topc @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (v2_pre_topc @ X11)
% 0.20/0.48          | ~ (l1_pre_topc @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.48          | (v1_tsep_1 @ X10 @ X11)
% 0.20/0.48          | ~ (v3_pre_topc @ (u1_struct_0 @ X10) @ X11)
% 0.20/0.48          | ~ (m1_pre_topc @ X10 @ X11))),
% 0.20/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.48         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.48         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.48         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['16'])).
% 0.20/0.48  thf(abstractness_v1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ( v1_pre_topc @ A ) =>
% 0.20/0.48         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_pre_topc @ X0)
% 0.20/0.48          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_pre_topc @ X0)
% 0.20/0.48          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.48  thf(dt_u1_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( u1_pre_topc @ A ) @ 
% 0.20/0.48         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.20/0.48          | ~ (l1_pre_topc @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.48  thf(free_g1_pre_topc, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.48       ( ![C:$i,D:$i]:
% 0.20/0.48         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.20/0.48           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.20/0.48          | ((X6) = (X4))
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.48      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X0)
% 0.20/0.48          | ((u1_pre_topc @ X0) = (X1))
% 0.20/0.48          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.48              != (g1_pre_topc @ X2 @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (v1_pre_topc @ X0)
% 0.20/0.48          | ((u1_pre_topc @ X0) = (X1))
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         (((u1_pre_topc @ (g1_pre_topc @ X2 @ X1)) = (X1))
% 0.20/0.48          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.20/0.48          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((~ (v1_pre_topc @ sk_C)
% 0.20/0.48        | ~ (l1_pre_topc @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.48        | ((u1_pre_topc @ 
% 0.20/0.48            (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.48            = (u1_pre_topc @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(fc6_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ( v1_pre_topc @
% 0.20/0.48           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.20/0.48         ( v2_pre_topc @
% 0.20/0.48           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X2 : $i]:
% 0.20/0.48         ((v1_pre_topc @ 
% 0.20/0.48           (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.20/0.48          | ~ (l1_pre_topc @ X2)
% 0.20/0.48          | ~ (v2_pre_topc @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (((v1_pre_topc @ sk_C) | ~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('40', plain, ((v1_pre_topc @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '40', '41', '42', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X1 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (u1_pre_topc @ X1) @ 
% 0.20/0.48           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.20/0.48          | ~ (l1_pre_topc @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.20/0.48        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.48      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_pre_topc @ sk_C) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.20/0.48          | ((X5) = (X3))
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.48      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((u1_struct_0 @ sk_B) = (X0))
% 0.20/0.48          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C))
% 0.20/0.48              != (g1_pre_topc @ X0 @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('52', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '40', '41', '42', '43'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((u1_struct_0 @ sk_B) = (X0)) | ((sk_C) != (g1_pre_topc @ X0 @ X1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['50', '53'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_C) != (X0))
% 0.20/0.48          | ~ (l1_pre_topc @ X0)
% 0.20/0.48          | ~ (v1_pre_topc @ X0)
% 0.20/0.48          | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '54'])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      ((((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))
% 0.20/0.48        | ~ (v1_pre_topc @ sk_C)
% 0.20/0.48        | ~ (l1_pre_topc @ sk_C))),
% 0.20/0.48      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.48  thf('57', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('58', plain, ((v1_pre_topc @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.48  thf('59', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['56', '57', '58'])).
% 0.20/0.48  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.20/0.48         | (v1_tsep_1 @ sk_B @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '25', '59', '60', '61'])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (((v1_tsep_1 @ sk_B @ sk_A))
% 0.20/0.48         <= (((v1_tsep_1 @ sk_C @ sk_A)) & 
% 0.20/0.48             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.20/0.48             ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '62'])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      ((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.48        | ~ (v1_tsep_1 @ sk_C @ sk_A)
% 0.20/0.48        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['64'])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      (~ ((v1_tsep_1 @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A)) | 
% 0.20/0.48       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['63', '65'])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (v2_pre_topc @ X11)
% 0.20/0.48          | ~ (l1_pre_topc @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.48          | (v3_pre_topc @ (u1_struct_0 @ X10) @ X11)
% 0.20/0.48          | ~ (v1_tsep_1 @ X10 @ X11)
% 0.20/0.48          | ~ (m1_pre_topc @ X10 @ X11))),
% 0.20/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.48         | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.48         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.20/0.48         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.48  thf('71', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['16'])).
% 0.20/0.48  thf('72', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['56', '57', '58'])).
% 0.20/0.48  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('75', plain,
% 0.20/0.48      (((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.20/0.48         | (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)))
% 0.20/0.48         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['70', '71', '72', '73', '74'])).
% 0.20/0.48  thf('76', plain,
% 0.20/0.48      (((v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A))
% 0.20/0.48         <= (((v1_tsep_1 @ sk_B @ sk_A)) & ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['67', '75'])).
% 0.20/0.48  thf('77', plain,
% 0.20/0.48      (((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.48         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('78', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (v2_pre_topc @ X11)
% 0.20/0.48          | ~ (l1_pre_topc @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.20/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.48          | (v1_tsep_1 @ X10 @ X11)
% 0.20/0.48          | ~ (v3_pre_topc @ (u1_struct_0 @ X10) @ X11)
% 0.20/0.48          | ~ (m1_pre_topc @ X10 @ X11))),
% 0.20/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.48  thf('79', plain,
% 0.20/0.48      (((~ (m1_pre_topc @ sk_C @ sk_A)
% 0.20/0.48         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.20/0.48         | (v1_tsep_1 @ sk_C @ sk_A)
% 0.20/0.48         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48         | ~ (v2_pre_topc @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.48  thf('80', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('83', plain,
% 0.20/0.48      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_C) @ sk_A)
% 0.20/0.48         | (v1_tsep_1 @ sk_C @ sk_A))) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.20/0.48  thf('84', plain,
% 0.20/0.48      (((v1_tsep_1 @ sk_C @ sk_A))
% 0.20/0.48         <= (((v1_tsep_1 @ sk_B @ sk_A)) & 
% 0.20/0.48             ((m1_pre_topc @ sk_B @ sk_A)) & 
% 0.20/0.48             ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['76', '83'])).
% 0.20/0.48  thf('85', plain,
% 0.20/0.48      ((~ (v1_tsep_1 @ sk_C @ sk_A)) <= (~ ((v1_tsep_1 @ sk_C @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['64'])).
% 0.20/0.48  thf('86', plain,
% 0.20/0.48      (((v1_tsep_1 @ sk_C @ sk_A)) | ~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 0.20/0.48       ~ ((m1_pre_topc @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.48  thf('87', plain,
% 0.20/0.48      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_C @ sk_A)) | 
% 0.20/0.48       ~ ((v1_tsep_1 @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['64'])).
% 0.20/0.48  thf('88', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['16'])).
% 0.20/0.48  thf('89', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['56', '57', '58'])).
% 0.20/0.48  thf(t12_tmap_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.20/0.48               ( ( ( B ) =
% 0.20/0.48                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.20/0.48                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('90', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (v2_pre_topc @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ((X7) != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.20/0.48          | ~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.48          | (m1_pre_topc @ X7 @ X9)
% 0.20/0.48          | ~ (l1_pre_topc @ X8)
% 0.20/0.48          | ~ (v2_pre_topc @ X8)
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.20/0.48  thf('91', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X9)
% 0.20/0.48          | ~ (v2_pre_topc @ X8)
% 0.20/0.48          | ~ (l1_pre_topc @ X8)
% 0.20/0.48          | (m1_pre_topc @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)) @ X9)
% 0.20/0.48          | ~ (m1_pre_topc @ X8 @ X9)
% 0.20/0.48          | ~ (l1_pre_topc @ 
% 0.20/0.48               (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.20/0.48          | ~ (v2_pre_topc @ 
% 0.20/0.48               (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['90'])).
% 0.20/0.48  thf('92', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))
% 0.20/0.48          | ~ (v2_pre_topc @ 
% 0.20/0.48               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.48          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.48          | (m1_pre_topc @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['89', '91'])).
% 0.20/0.48  thf('93', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '40', '41', '42', '43'])).
% 0.20/0.48  thf('94', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf('95', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['56', '57', '58'])).
% 0.20/0.48  thf('96', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.48  thf('97', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('98', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['56', '57', '58'])).
% 0.20/0.48  thf('99', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '40', '41', '42', '43'])).
% 0.20/0.48  thf('100', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.48  thf('101', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('102', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['56', '57', '58'])).
% 0.20/0.48  thf('103', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '40', '41', '42', '43'])).
% 0.20/0.48  thf('104', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.48  thf('105', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('106', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('107', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ sk_B @ X0)
% 0.20/0.48          | (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('demod', [status(thm)],
% 0.20/0.48                ['92', '93', '96', '97', '98', '99', '100', '101', '102', 
% 0.20/0.48                 '103', '104', '105', '106'])).
% 0.20/0.48  thf('108', plain,
% 0.20/0.48      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_C @ sk_A)))
% 0.20/0.48         <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['88', '107'])).
% 0.20/0.48  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('110', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.48  thf('111', plain,
% 0.20/0.48      ((~ (m1_pre_topc @ sk_C @ sk_A)) <= (~ ((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['64'])).
% 0.20/0.48  thf('112', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_C @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['110', '111'])).
% 0.20/0.48  thf('113', plain,
% 0.20/0.48      (((v1_tsep_1 @ sk_C @ sk_A)) | ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('114', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_C @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('115', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['114'])).
% 0.20/0.48  thf('116', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_C @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('117', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['56', '57', '58'])).
% 0.20/0.48  thf('118', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (v2_pre_topc @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ((X7) != (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.20/0.48          | ~ (m1_pre_topc @ X7 @ X9)
% 0.20/0.48          | (m1_pre_topc @ X8 @ X9)
% 0.20/0.48          | ~ (l1_pre_topc @ X8)
% 0.20/0.48          | ~ (v2_pre_topc @ X8)
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.20/0.48  thf('119', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ X9)
% 0.20/0.48          | ~ (v2_pre_topc @ X8)
% 0.20/0.48          | ~ (l1_pre_topc @ X8)
% 0.20/0.48          | (m1_pre_topc @ X8 @ X9)
% 0.20/0.48          | ~ (m1_pre_topc @ 
% 0.20/0.48               (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)) @ X9)
% 0.20/0.48          | ~ (l1_pre_topc @ 
% 0.20/0.48               (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.20/0.48          | ~ (v2_pre_topc @ 
% 0.20/0.48               (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['118'])).
% 0.20/0.48  thf('120', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ 
% 0.20/0.48             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_B)))
% 0.20/0.48          | ~ (v2_pre_topc @ 
% 0.20/0.48               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.48          | ~ (m1_pre_topc @ 
% 0.20/0.48               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.20/0.48          | (m1_pre_topc @ sk_B @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['117', '119'])).
% 0.20/0.48  thf('121', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '40', '41', '42', '43'])).
% 0.20/0.48  thf('122', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.48  thf('123', plain, ((l1_pre_topc @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('124', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['56', '57', '58'])).
% 0.20/0.48  thf('125', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '40', '41', '42', '43'])).
% 0.20/0.48  thf('126', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.48  thf('127', plain, ((v2_pre_topc @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('128', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('simplify_reflect+', [status(thm)], ['56', '57', '58'])).
% 0.20/0.48  thf('129', plain, (((u1_pre_topc @ sk_C) = (u1_pre_topc @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '40', '41', '42', '43'])).
% 0.20/0.48  thf('130', plain,
% 0.20/0.48      (((sk_C) = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['94', '95'])).
% 0.20/0.48  thf('131', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('132', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('133', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.48          | (m1_pre_topc @ sk_B @ X0)
% 0.20/0.48          | ~ (l1_pre_topc @ X0))),
% 0.20/0.48      inference('demod', [status(thm)],
% 0.20/0.48                ['120', '121', '122', '123', '124', '125', '126', '127', 
% 0.20/0.48                 '128', '129', '130', '131', '132'])).
% 0.20/0.48  thf('134', plain,
% 0.20/0.48      (((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A)))
% 0.20/0.48         <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['116', '133'])).
% 0.20/0.48  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('136', plain,
% 0.20/0.48      (((m1_pre_topc @ sk_B @ sk_A)) <= (((m1_pre_topc @ sk_C @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['134', '135'])).
% 0.20/0.48  thf('137', plain,
% 0.20/0.48      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['64'])).
% 0.20/0.48  thf('138', plain,
% 0.20/0.48      (~ ((m1_pre_topc @ sk_C @ sk_A)) | ((m1_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['136', '137'])).
% 0.20/0.48  thf('139', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)],
% 0.20/0.48                ['66', '86', '87', '112', '113', '115', '138'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
