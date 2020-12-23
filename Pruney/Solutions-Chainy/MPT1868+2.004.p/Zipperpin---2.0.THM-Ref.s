%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FcEfSdltdJ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 220 expanded)
%              Number of leaves         :   24 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  713 (2377 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(t36_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('3',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( X15
       != ( u1_struct_0 @ X13 ) )
      | ~ ( v1_tdlat_3 @ X13 )
      | ( v2_tex_2 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X13 ) @ X14 )
      | ~ ( v1_tdlat_3 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('16',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(cc25_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ( v7_struct_0 @ B )
              & ( v2_pre_topc @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ( v1_tdlat_3 @ B )
              & ( v2_tdlat_3 @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v1_tdlat_3 @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( v7_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc25_tex_2])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('22',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19','26'])).

thf('28',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('30',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('39',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['36','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('53',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf(d4_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_tex_2 @ A @ B ) )
              <=> ( ( u1_struct_0 @ C )
                  = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('58',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ( X8
       != ( k1_tex_2 @ X7 @ X6 ) )
      | ( ( u1_struct_0 @ X8 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X7 ) @ X6 ) )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( v1_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X7 @ X6 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X7 @ X6 ) @ X7 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X7 @ X6 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X7 ) @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['50','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FcEfSdltdJ
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:26:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 29 iterations in 0.020s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.21/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.48  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.21/0.48  thf(t36_tex_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48              ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t36_tex_2])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (~ (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_k1_tex_2, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.48         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.48         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X9)
% 0.21/0.48          | (v2_struct_0 @ X9)
% 0.21/0.48          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.21/0.48          | (m1_pre_topc @ (k1_tex_2 @ X9 @ X10) @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf(t1_tsep_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48           ( m1_subset_1 @
% 0.21/0.48             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X2 @ X3)
% 0.21/0.48          | (m1_subset_1 @ (u1_struct_0 @ X2) @ 
% 0.21/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.21/0.48          | ~ (l1_pre_topc @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.21/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf(t26_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.48                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X13)
% 0.21/0.48          | ~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.48          | ((X15) != (u1_struct_0 @ X13))
% 0.21/0.48          | ~ (v1_tdlat_3 @ X13)
% 0.21/0.48          | (v2_tex_2 @ X15 @ X14)
% 0.21/0.48          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.48          | ~ (l1_pre_topc @ X14)
% 0.21/0.48          | (v2_struct_0 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X14)
% 0.21/0.48          | ~ (l1_pre_topc @ X14)
% 0.21/0.48          | ~ (m1_subset_1 @ (u1_struct_0 @ X13) @ 
% 0.21/0.48               (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.48          | (v2_tex_2 @ (u1_struct_0 @ X13) @ X14)
% 0.21/0.48          | ~ (v1_tdlat_3 @ X13)
% 0.21/0.48          | ~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.48          | (v2_struct_0 @ X13))),
% 0.21/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '13'])).
% 0.21/0.48  thf('15', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('16', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf(cc25_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48           ( ( ( ~( v2_struct_0 @ B ) ) & ( v7_struct_0 @ B ) & 
% 0.21/0.48               ( v2_pre_topc @ B ) ) =>
% 0.21/0.48             ( ( ~( v2_struct_0 @ B ) ) & ( v1_tdlat_3 @ B ) & 
% 0.21/0.48               ( v2_tdlat_3 @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X4 @ X5)
% 0.21/0.48          | (v1_tdlat_3 @ X4)
% 0.21/0.48          | ~ (v2_pre_topc @ X4)
% 0.21/0.48          | ~ (v7_struct_0 @ X4)
% 0.21/0.48          | (v2_struct_0 @ X4)
% 0.21/0.48          | ~ (l1_pre_topc @ X5)
% 0.21/0.48          | (v2_struct_0 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc25_tex_2])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(fc2_tex_2, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.48         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.48         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X11)
% 0.21/0.48          | (v2_struct_0 @ X11)
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.21/0.48          | (v7_struct_0 @ (k1_tex_2 @ X11 @ X12)))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['18', '19', '26'])).
% 0.21/0.48  thf('28', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf(cc1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.48          | (v2_pre_topc @ X0)
% 0.21/0.48          | ~ (l1_pre_topc @ X1)
% 0.21/0.48          | ~ (v2_pre_topc @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('33', plain, ((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '33'])).
% 0.21/0.48  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X9)
% 0.21/0.48          | (v2_struct_0 @ X9)
% 0.21/0.48          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.21/0.48          | ~ (v2_struct_0 @ (k1_tex_2 @ X9 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.48  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('43', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf('44', plain, ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['36', '43'])).
% 0.21/0.48  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15', '44', '45'])).
% 0.21/0.48  thf('47', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A))),
% 0.21/0.48      inference('clc', [status(thm)], ['46', '47'])).
% 0.21/0.48  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      ((v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf('51', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         (~ (l1_pre_topc @ X9)
% 0.21/0.48          | (v2_struct_0 @ X9)
% 0.21/0.48          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.21/0.48          | (v1_pre_topc @ (k1_tex_2 @ X9 @ X10)))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.48  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.48  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('57', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.48  thf(d4_tex_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.21/0.48                 ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.48               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.21/0.48                 ( ( u1_struct_0 @ C ) =
% 0.21/0.48                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.21/0.48          | ((X8) != (k1_tex_2 @ X7 @ X6))
% 0.21/0.48          | ((u1_struct_0 @ X8) = (k6_domain_1 @ (u1_struct_0 @ X7) @ X6))
% 0.21/0.48          | ~ (m1_pre_topc @ X8 @ X7)
% 0.21/0.48          | ~ (v1_pre_topc @ X8)
% 0.21/0.48          | (v2_struct_0 @ X8)
% 0.21/0.48          | ~ (l1_pre_topc @ X7)
% 0.21/0.48          | (v2_struct_0 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X7)
% 0.21/0.48          | ~ (l1_pre_topc @ X7)
% 0.21/0.48          | (v2_struct_0 @ (k1_tex_2 @ X7 @ X6))
% 0.21/0.48          | ~ (v1_pre_topc @ (k1_tex_2 @ X7 @ X6))
% 0.21/0.48          | ~ (m1_pre_topc @ (k1_tex_2 @ X7 @ X6) @ X7)
% 0.21/0.48          | ((u1_struct_0 @ (k1_tex_2 @ X7 @ X6))
% 0.21/0.48              = (k6_domain_1 @ (u1_struct_0 @ X7) @ X6))
% 0.21/0.48          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.48        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['57', '59'])).
% 0.21/0.48  thf('61', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('62', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('64', plain,
% 0.21/0.48      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.21/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.21/0.48  thf('65', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf('66', plain,
% 0.21/0.48      (((v2_struct_0 @ sk_A)
% 0.21/0.48        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.21/0.48      inference('clc', [status(thm)], ['64', '65'])).
% 0.21/0.48  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('68', plain,
% 0.21/0.48      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.21/0.48         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['66', '67'])).
% 0.21/0.48  thf('69', plain,
% 0.21/0.48      ((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['50', '68'])).
% 0.21/0.48  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
