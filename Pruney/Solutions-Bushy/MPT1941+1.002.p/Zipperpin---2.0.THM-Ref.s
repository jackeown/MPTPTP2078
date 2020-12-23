%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1941+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aNjeuLC4nS

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:35 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 934 expanded)
%              Number of leaves         :   35 ( 287 expanded)
%              Depth                    :   19
%              Number of atoms          :  984 (13345 expanded)
%              Number of equality atoms :   36 ( 395 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(a_2_0_yellow_6_type,type,(
    a_2_0_yellow_6: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k9_yellow_6_type,type,(
    k9_yellow_6: $i > $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(t39_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
              <=> ( ( r2_hidden @ B @ C )
                  & ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ ( u1_struct_0 @ ( k9_yellow_6 @ A @ B ) ) )
                <=> ( ( r2_hidden @ B @ C )
                    & ( v3_pre_topc @ C @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_yellow_6])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_0_yellow_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v2_pre_topc @ B )
        & ( l1_pre_topc @ B )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( r2_hidden @ A @ ( a_2_0_yellow_6 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( v3_pre_topc @ D @ B )
            & ( r2_hidden @ C @ D )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ X13 @ ( a_2_0_yellow_6 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X13 != X14 )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( v3_pre_topc @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow_6])).

thf('4',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( v3_pre_topc @ X14 @ X11 )
      | ~ ( r2_hidden @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ X14 @ ( a_2_0_yellow_6 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k9_yellow_6 @ A @ B )
            = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ A @ B ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X2 ) )
      | ( ( k9_yellow_6 @ X2 @ X1 )
        = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ X2 @ X1 ) ) ) )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( v2_pre_topc @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d17_yellow_6])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k9_yellow_6 @ sk_A @ sk_B )
      = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k9_yellow_6 @ sk_A @ sk_B )
      = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k9_yellow_6 @ sk_A @ sk_B )
    = ( k7_lattice3 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t12_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( u1_struct_0 @ A )
        = ( u1_struct_0 @ ( k7_lattice3 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X19: $i] :
      ( ( ( u1_struct_0 @ X19 )
        = ( u1_struct_0 @ ( k7_lattice3 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_yellow_6])).

thf('19',plain,
    ( ( ( u1_struct_0 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) )
      = ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('21',plain,
    ( ( u1_struct_0 @ ( k2_yellow_1 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) )
    = ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_orders_2 @ X0 )
      | ( X0
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf(dt_k1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k1_yellow_1 @ A ) @ A )
      & ( v8_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v4_relat_2 @ ( k1_yellow_1 @ A ) )
      & ( v1_relat_2 @ ( k1_yellow_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_1])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( g1_orders_2 @ X17 @ X18 )
       != ( g1_orders_2 @ X15 @ X16 ) )
      | ( X17 = X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( g1_orders_2 @ X0 @ ( k1_yellow_1 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k2_yellow_1 @ A )
      = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( ( k2_yellow_1 @ X3 )
      = ( g1_orders_2 @ X3 @ ( k1_yellow_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( ( k2_yellow_1 @ X0 )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_yellow_1 @ X1 )
       != X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ( X1
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) )
      | ~ ( v1_orders_2 @ ( k2_yellow_1 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X10: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('31',plain,(
    ! [X9: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('32',plain,(
    ! [X1: $i] :
      ( X1
      = ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference('simplify_reflect+',[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( a_2_0_yellow_6 @ sk_A @ sk_B )
    = ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ X12 @ ( sk_D @ X12 @ X11 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( a_2_0_yellow_6 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow_6])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_B @ ( sk_D @ sk_B @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( X13
        = ( sk_D @ X12 @ X11 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( a_2_0_yellow_6 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow_6])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_C
      = ( sk_D @ sk_B @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','55'])).

thf('57',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( v3_pre_topc @ ( sk_D @ X12 @ X11 @ X13 ) @ X11 )
      | ~ ( r2_hidden @ X13 @ ( a_2_0_yellow_6 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_yellow_6])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( sk_D @ sk_B @ sk_A @ X0 ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( sk_D @ sk_B @ sk_A @ X0 ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( sk_D @ sk_B @ sk_A @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v3_pre_topc @ ( sk_D @ sk_B @ sk_A @ sk_C ) @ sk_A )
   <= ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,
    ( ( sk_C
      = ( sk_D @ sk_B @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('71',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('73',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
    | ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['57'])).

thf('75',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('76',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['59','73','74','75'])).

thf('77',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['9','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6','7','77'])).

thf('79',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','78'])).

thf('80',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['34'])).

thf('81',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('82',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['59','73','74','81'])).

thf('83',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','83'])).

thf('85',plain,
    ( ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['57'])).

thf('86',plain,
    ( ( a_2_0_yellow_6 @ sk_A @ sk_B )
    = ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','32'])).

thf('87',plain,
    ( ~ ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( r2_hidden @ sk_C @ ( u1_struct_0 @ ( k9_yellow_6 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['59','73','74'])).

thf('89',plain,(
    ~ ( r2_hidden @ sk_C @ ( a_2_0_yellow_6 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['87','88'])).

thf('90',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['84','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90'])).


%------------------------------------------------------------------------------
