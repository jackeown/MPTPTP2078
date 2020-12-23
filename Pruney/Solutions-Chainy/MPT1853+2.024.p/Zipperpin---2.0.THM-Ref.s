%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhgCUymmsh

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 393 expanded)
%              Number of leaves         :   26 ( 117 expanded)
%              Depth                    :   19
%              Number of atoms          :  988 (5186 expanded)
%              Number of equality atoms :   15 (  45 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(t20_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
          <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
            <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_tex_2])).

thf('0',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t9_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X17 ) @ X16 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v7_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_tex_2])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_struct_0 @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v7_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('17',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf(cc10_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ~ ( v2_struct_0 @ B )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tex_2 @ B @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ~ ( v1_tex_2 @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v7_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('29',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['26','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','36'])).

thf('38',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('39',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('40',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( ( sk_C @ X5 @ X6 )
        = ( u1_struct_0 @ X5 ) )
      | ( v1_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( m1_subset_1 @ ( sk_C @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X9 = X8 )
      | ( v1_subset_1 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('53',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( v1_subset_1 @ ( sk_C @ X5 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ( v1_tex_2 @ X5 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('55',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('58',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['46','61'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X15 ) @ X14 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v7_struct_0 @ X15 )
      | ~ ( l1_struct_0 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['46','61'])).

thf('66',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('67',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('72',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('74',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('75',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['46','61'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','72','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','37','38','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhgCUymmsh
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 61 iterations in 0.030s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.48  thf(t20_tex_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.48             ( v1_subset_1 @
% 0.21/0.48               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.48                ( v1_subset_1 @
% 0.21/0.48                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.48                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48           (u1_struct_0 @ sk_A))
% 0.21/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (~
% 0.21/0.48       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48         (u1_struct_0 @ sk_A))) | 
% 0.21/0.48       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t9_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 0.21/0.48         ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( v1_subset_1 @
% 0.21/0.48             ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.48          | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X17) @ X16) @ 
% 0.21/0.48             (u1_struct_0 @ X17))
% 0.21/0.48          | ~ (l1_struct_0 @ X17)
% 0.21/0.48          | (v7_struct_0 @ X17)
% 0.21/0.48          | (v2_struct_0 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [t9_tex_2])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (v7_struct_0 @ sk_A)
% 0.21/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.48        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48           (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_l1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.48  thf('6', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (v7_struct_0 @ sk_A)
% 0.21/0.48        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48           (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '7'])).
% 0.21/0.48  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48         (u1_struct_0 @ sk_A))
% 0.21/0.48        | (v7_struct_0 @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48           (u1_struct_0 @ sk_A)))
% 0.21/0.48         <= (~
% 0.21/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48               (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((v7_struct_0 @ sk_A))
% 0.21/0.48         <= (~
% 0.21/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48               (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48         (u1_struct_0 @ sk_A))
% 0.21/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['13'])).
% 0.21/0.48  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_k1_tex_2, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.48         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.48         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X10)
% 0.21/0.48          | (v2_struct_0 @ X10)
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.48          | (m1_pre_topc @ (k1_tex_2 @ X10 @ X11) @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf(cc10_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.21/0.48             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X3 @ X4)
% 0.21/0.48          | ~ (v1_tex_2 @ X3 @ X4)
% 0.21/0.48          | (v2_struct_0 @ X3)
% 0.21/0.48          | ~ (l1_pre_topc @ X4)
% 0.21/0.48          | ~ (v7_struct_0 @ X4)
% 0.21/0.48          | (v2_struct_0 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v7_struct_0 @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v7_struct_0 @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48         | ~ (v7_struct_0 @ sk_A)
% 0.21/0.48         | (v2_struct_0 @ sk_A)))
% 0.21/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '25'])).
% 0.21/0.48  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X10)
% 0.21/0.48          | (v2_struct_0 @ X10)
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.48          | ~ (v2_struct_0 @ (k1_tex_2 @ X10 @ X11)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.21/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['26', '33'])).
% 0.21/0.48  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      ((~ (v7_struct_0 @ sk_A))
% 0.21/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48         (u1_struct_0 @ sk_A))) | 
% 0.21/0.48       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48         (u1_struct_0 @ sk_A))) | 
% 0.21/0.48       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('split', [status(esa)], ['13'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48         (u1_struct_0 @ sk_A)))
% 0.21/0.48         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.48               (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('split', [status(esa)], ['13'])).
% 0.21/0.48  thf('40', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf(d3_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48           ( ( v1_tex_2 @ B @ A ) <=>
% 0.21/0.48             ( ![C:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.48                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X5 @ X6)
% 0.21/0.48          | ((sk_C @ X5 @ X6) = (u1_struct_0 @ X5))
% 0.21/0.48          | (v1_tex_2 @ X5 @ X6)
% 0.21/0.48          | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.21/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.21/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.48  thf('47', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X5 @ X6)
% 0.21/0.48          | (m1_subset_1 @ (sk_C @ X5 @ X6) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.48          | (v1_tex_2 @ X5 @ X6)
% 0.21/0.48          | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.48  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf(d7_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.48       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]:
% 0.21/0.48         (((X9) = (X8))
% 0.21/0.48          | (v1_subset_1 @ X9 @ X8)
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | (v1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.21/0.48           (u1_struct_0 @ sk_A))
% 0.21/0.48        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X5 @ X6)
% 0.21/0.48          | ~ (v1_subset_1 @ (sk_C @ X5 @ X6) @ (u1_struct_0 @ X6))
% 0.21/0.48          | (v1_tex_2 @ X5 @ X6)
% 0.21/0.48          | ~ (l1_pre_topc @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.48  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('57', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A))
% 0.21/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.21/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('61', plain,
% 0.21/0.48      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.21/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.21/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['46', '61'])).
% 0.21/0.48  thf(t8_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( ~( ( v1_subset_1 @
% 0.21/0.48                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.48                  ( u1_struct_0 @ A ) ) & 
% 0.21/0.48                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('63', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.21/0.48          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X15) @ X14) @ 
% 0.21/0.48               (u1_struct_0 @ X15))
% 0.21/0.48          | ~ (v7_struct_0 @ X15)
% 0.21/0.48          | ~ (l1_struct_0 @ X15)
% 0.21/0.48          | (v2_struct_0 @ X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.21/0.48  thf('64', plain,
% 0.21/0.48      ((![X0 : $i]:
% 0.21/0.48          (~ (v1_subset_1 @ 
% 0.21/0.48              (k6_domain_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ X0) @ 
% 0.21/0.48              (u1_struct_0 @ sk_A))
% 0.21/0.48           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48           | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48           | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))
% 0.21/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.48  thf('65', plain,
% 0.21/0.48      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.21/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['46', '61'])).
% 0.21/0.48  thf('66', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf(dt_m1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X1 @ X2) | (l1_pre_topc @ X1) | ~ (l1_pre_topc @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.48  thf('68', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.48  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.49  thf('71', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('72', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.49  thf('73', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(fc2_tex_2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.49         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.49         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X12)
% 0.21/0.49          | (v2_struct_0 @ X12)
% 0.21/0.49          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.21/0.49          | (v7_struct_0 @ (k1_tex_2 @ X12 @ X13)))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49        | (v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.49  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['75', '76'])).
% 0.21/0.49  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('79', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['77', '78'])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['46', '61'])).
% 0.21/0.49  thf('81', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.21/0.49              (u1_struct_0 @ sk_A))
% 0.21/0.49           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.49           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['64', '65', '72', '79', '80'])).
% 0.21/0.49  thf('82', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('83', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49           | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.21/0.49                (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['81', '82'])).
% 0.21/0.49  thf('84', plain,
% 0.21/0.49      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) & 
% 0.21/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49               (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '83'])).
% 0.21/0.49  thf('85', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('86', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.21/0.49         (u1_struct_0 @ sk_A))) | 
% 0.21/0.49       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.49  thf('87', plain, ($false),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['1', '37', '38', '86'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
