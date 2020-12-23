%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dklhiSS5Nz

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 300 expanded)
%              Number of leaves         :   22 (  92 expanded)
%              Depth                    :   17
%              Number of atoms          :  726 (3479 expanded)
%              Number of equality atoms :   14 (  32 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X7 @ X8 ) @ X7 ) ) ),
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

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('14',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ( X6
       != ( k1_tex_2 @ X5 @ X4 ) )
      | ( ( u1_struct_0 @ X6 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X5 ) @ X4 ) )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ~ ( v1_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X5 @ X4 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X5 @ X4 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X5 @ X4 ) @ X5 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X5 @ X4 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X5 ) @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('26',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X7 @ X8 ) ) ) ),
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
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['26','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','36'])).

thf('38',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

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

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( u1_struct_0 @ X11 ) )
      | ~ ( v1_tdlat_3 @ X11 )
      | ( v2_tex_2 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X11 ) @ X12 )
      | ~ ( v1_tdlat_3 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X12 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) )
           => ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) )
              & ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( v1_tdlat_3 @ ( k1_tex_2 @ X10 @ X9 ) )
      | ~ ( v2_pre_topc @ ( k1_tex_2 @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t24_tex_2])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('51',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    v1_tdlat_3 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['48','54'])).

thf('56',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('65',plain,(
    v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dklhiSS5Nz
% 0.16/0.37  % Computer   : n019.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 15:39:38 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.47  % Solved by: fo/fo7.sh
% 0.23/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.47  % done 34 iterations in 0.019s
% 0.23/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.47  % SZS output start Refutation
% 0.23/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.23/0.47  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.23/0.47  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.23/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.23/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.47  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.23/0.47  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.23/0.47  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.23/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.47  thf(t36_tex_2, conjecture,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.47       ( ![B:$i]:
% 0.23/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.47           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.23/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.47    (~( ![A:$i]:
% 0.23/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.47            ( l1_pre_topc @ A ) ) =>
% 0.23/0.47          ( ![B:$i]:
% 0.23/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.47              ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )),
% 0.23/0.47    inference('cnf.neg', [status(esa)], [t36_tex_2])).
% 0.23/0.47  thf('0', plain,
% 0.23/0.47      (~ (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf(dt_k1_tex_2, axiom,
% 0.23/0.47    (![A:$i,B:$i]:
% 0.23/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.23/0.47         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.47       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.23/0.47         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.23/0.47         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.23/0.47  thf('2', plain,
% 0.23/0.47      (![X7 : $i, X8 : $i]:
% 0.23/0.47         (~ (l1_pre_topc @ X7)
% 0.23/0.47          | (v2_struct_0 @ X7)
% 0.23/0.47          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.23/0.47          | (m1_pre_topc @ (k1_tex_2 @ X7 @ X8) @ X7))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.23/0.47  thf('3', plain,
% 0.23/0.47      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.23/0.47        | (v2_struct_0 @ sk_A)
% 0.23/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.47  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('5', plain,
% 0.23/0.47      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.23/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.47  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('7', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.23/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.23/0.47  thf(t1_tsep_1, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( l1_pre_topc @ A ) =>
% 0.23/0.47       ( ![B:$i]:
% 0.23/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.23/0.47           ( m1_subset_1 @
% 0.23/0.47             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.23/0.47  thf('8', plain,
% 0.23/0.47      (![X2 : $i, X3 : $i]:
% 0.23/0.47         (~ (m1_pre_topc @ X2 @ X3)
% 0.23/0.47          | (m1_subset_1 @ (u1_struct_0 @ X2) @ 
% 0.23/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.23/0.47          | ~ (l1_pre_topc @ X3))),
% 0.23/0.47      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.23/0.47  thf('9', plain,
% 0.23/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.23/0.47        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.23/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.47  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('11', plain,
% 0.23/0.47      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.23/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.47  thf('12', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('13', plain,
% 0.23/0.47      (![X7 : $i, X8 : $i]:
% 0.23/0.47         (~ (l1_pre_topc @ X7)
% 0.23/0.47          | (v2_struct_0 @ X7)
% 0.23/0.47          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.23/0.47          | (v1_pre_topc @ (k1_tex_2 @ X7 @ X8)))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.23/0.47  thf('14', plain,
% 0.23/0.47      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47        | (v2_struct_0 @ sk_A)
% 0.23/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.47  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('16', plain,
% 0.23/0.47      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.23/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.23/0.47  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('18', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.23/0.47      inference('clc', [status(thm)], ['16', '17'])).
% 0.23/0.47  thf(d4_tex_2, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.47       ( ![B:$i]:
% 0.23/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.47           ( ![C:$i]:
% 0.23/0.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.23/0.47                 ( m1_pre_topc @ C @ A ) ) =>
% 0.23/0.47               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.23/0.47                 ( ( u1_struct_0 @ C ) =
% 0.23/0.47                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.23/0.47  thf('19', plain,
% 0.23/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.47         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.23/0.47          | ((X6) != (k1_tex_2 @ X5 @ X4))
% 0.23/0.47          | ((u1_struct_0 @ X6) = (k6_domain_1 @ (u1_struct_0 @ X5) @ X4))
% 0.23/0.47          | ~ (m1_pre_topc @ X6 @ X5)
% 0.23/0.47          | ~ (v1_pre_topc @ X6)
% 0.23/0.47          | (v2_struct_0 @ X6)
% 0.23/0.47          | ~ (l1_pre_topc @ X5)
% 0.23/0.47          | (v2_struct_0 @ X5))),
% 0.23/0.47      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.23/0.47  thf('20', plain,
% 0.23/0.47      (![X4 : $i, X5 : $i]:
% 0.23/0.47         ((v2_struct_0 @ X5)
% 0.23/0.47          | ~ (l1_pre_topc @ X5)
% 0.23/0.47          | (v2_struct_0 @ (k1_tex_2 @ X5 @ X4))
% 0.23/0.47          | ~ (v1_pre_topc @ (k1_tex_2 @ X5 @ X4))
% 0.23/0.47          | ~ (m1_pre_topc @ (k1_tex_2 @ X5 @ X4) @ X5)
% 0.23/0.47          | ((u1_struct_0 @ (k1_tex_2 @ X5 @ X4))
% 0.23/0.47              = (k6_domain_1 @ (u1_struct_0 @ X5) @ X4))
% 0.23/0.47          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5)))),
% 0.23/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.23/0.47  thf('21', plain,
% 0.23/0.47      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.23/0.47        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.23/0.47        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.23/0.47        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.47        | (v2_struct_0 @ sk_A))),
% 0.23/0.47      inference('sup-', [status(thm)], ['18', '20'])).
% 0.23/0.47  thf('22', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('24', plain,
% 0.23/0.47      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.23/0.47        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.23/0.47        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47        | (v2_struct_0 @ sk_A))),
% 0.23/0.47      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.23/0.47  thf('25', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.23/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.23/0.47  thf('26', plain,
% 0.23/0.47      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.23/0.47        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47        | (v2_struct_0 @ sk_A))),
% 0.23/0.47      inference('demod', [status(thm)], ['24', '25'])).
% 0.23/0.47  thf('27', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('28', plain,
% 0.23/0.47      (![X7 : $i, X8 : $i]:
% 0.23/0.47         (~ (l1_pre_topc @ X7)
% 0.23/0.47          | (v2_struct_0 @ X7)
% 0.23/0.47          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.23/0.47          | ~ (v2_struct_0 @ (k1_tex_2 @ X7 @ X8)))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.23/0.47  thf('29', plain,
% 0.23/0.47      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47        | (v2_struct_0 @ sk_A)
% 0.23/0.47        | ~ (l1_pre_topc @ sk_A))),
% 0.23/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.47  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('31', plain,
% 0.23/0.47      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.23/0.47      inference('demod', [status(thm)], ['29', '30'])).
% 0.23/0.47  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('33', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.23/0.47      inference('clc', [status(thm)], ['31', '32'])).
% 0.23/0.47  thf('34', plain,
% 0.23/0.47      (((v2_struct_0 @ sk_A)
% 0.23/0.47        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.23/0.47      inference('clc', [status(thm)], ['26', '33'])).
% 0.23/0.47  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('36', plain,
% 0.23/0.47      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.23/0.47      inference('clc', [status(thm)], ['34', '35'])).
% 0.23/0.47  thf('37', plain,
% 0.23/0.47      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.47      inference('demod', [status(thm)], ['11', '36'])).
% 0.23/0.47  thf('38', plain,
% 0.23/0.47      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.23/0.47      inference('clc', [status(thm)], ['34', '35'])).
% 0.23/0.47  thf(t26_tex_2, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.47       ( ![B:$i]:
% 0.23/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.23/0.47           ( ![C:$i]:
% 0.23/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.47               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.23/0.47                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.23/0.47  thf('39', plain,
% 0.23/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.47         ((v2_struct_0 @ X11)
% 0.23/0.47          | ~ (m1_pre_topc @ X11 @ X12)
% 0.23/0.47          | ((X13) != (u1_struct_0 @ X11))
% 0.23/0.47          | ~ (v1_tdlat_3 @ X11)
% 0.23/0.47          | (v2_tex_2 @ X13 @ X12)
% 0.23/0.47          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.23/0.47          | ~ (l1_pre_topc @ X12)
% 0.23/0.47          | (v2_struct_0 @ X12))),
% 0.23/0.47      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.23/0.47  thf('40', plain,
% 0.23/0.47      (![X11 : $i, X12 : $i]:
% 0.23/0.47         ((v2_struct_0 @ X12)
% 0.23/0.47          | ~ (l1_pre_topc @ X12)
% 0.23/0.47          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.23/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.23/0.47          | (v2_tex_2 @ (u1_struct_0 @ X11) @ X12)
% 0.23/0.47          | ~ (v1_tdlat_3 @ X11)
% 0.23/0.47          | ~ (m1_pre_topc @ X11 @ X12)
% 0.23/0.47          | (v2_struct_0 @ X11))),
% 0.23/0.47      inference('simplify', [status(thm)], ['39'])).
% 0.23/0.47  thf('41', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.47          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.23/0.47          | ~ (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47          | (v2_tex_2 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ X0)
% 0.23/0.47          | ~ (l1_pre_topc @ X0)
% 0.23/0.47          | (v2_struct_0 @ X0))),
% 0.23/0.47      inference('sup-', [status(thm)], ['38', '40'])).
% 0.23/0.47  thf('42', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf(t24_tex_2, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.47       ( ![B:$i]:
% 0.23/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.47           ( ( v2_pre_topc @ ( k1_tex_2 @ A @ B ) ) =>
% 0.23/0.47             ( ( v1_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.23/0.47               ( v2_tdlat_3 @ ( k1_tex_2 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.47  thf('43', plain,
% 0.23/0.47      (![X9 : $i, X10 : $i]:
% 0.23/0.47         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.23/0.47          | (v1_tdlat_3 @ (k1_tex_2 @ X10 @ X9))
% 0.23/0.47          | ~ (v2_pre_topc @ (k1_tex_2 @ X10 @ X9))
% 0.23/0.47          | ~ (l1_pre_topc @ X10)
% 0.23/0.47          | (v2_struct_0 @ X10))),
% 0.23/0.47      inference('cnf', [status(esa)], [t24_tex_2])).
% 0.23/0.47  thf('44', plain,
% 0.23/0.47      (((v2_struct_0 @ sk_A)
% 0.23/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.47        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['42', '43'])).
% 0.23/0.47  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('46', plain,
% 0.23/0.47      (((v2_struct_0 @ sk_A)
% 0.23/0.47        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47        | (v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.23/0.47      inference('demod', [status(thm)], ['44', '45'])).
% 0.23/0.47  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('48', plain,
% 0.23/0.47      (((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47        | ~ (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.23/0.47      inference('clc', [status(thm)], ['46', '47'])).
% 0.23/0.47  thf('49', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.23/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.23/0.47  thf(cc1_pre_topc, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.47       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.23/0.47  thf('50', plain,
% 0.23/0.47      (![X0 : $i, X1 : $i]:
% 0.23/0.47         (~ (m1_pre_topc @ X0 @ X1)
% 0.23/0.47          | (v2_pre_topc @ X0)
% 0.23/0.47          | ~ (l1_pre_topc @ X1)
% 0.23/0.47          | ~ (v2_pre_topc @ X1))),
% 0.23/0.47      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.23/0.47  thf('51', plain,
% 0.23/0.47      ((~ (v2_pre_topc @ sk_A)
% 0.23/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.47        | (v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['49', '50'])).
% 0.23/0.47  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('54', plain, ((v2_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.23/0.47      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.23/0.47  thf('55', plain, ((v1_tdlat_3 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.23/0.47      inference('demod', [status(thm)], ['48', '54'])).
% 0.23/0.47  thf('56', plain,
% 0.23/0.47      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.23/0.47      inference('clc', [status(thm)], ['34', '35'])).
% 0.23/0.47  thf('57', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.23/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.23/0.47          | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.23/0.47          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ X0)
% 0.23/0.47          | ~ (l1_pre_topc @ X0)
% 0.23/0.47          | (v2_struct_0 @ X0))),
% 0.23/0.47      inference('demod', [status(thm)], ['41', '55', '56'])).
% 0.23/0.47  thf('58', plain,
% 0.23/0.47      (((v2_struct_0 @ sk_A)
% 0.23/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.47        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.23/0.47        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.23/0.47        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['37', '57'])).
% 0.23/0.47  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('60', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.23/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.23/0.47  thf('61', plain,
% 0.23/0.47      (((v2_struct_0 @ sk_A)
% 0.23/0.47        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.23/0.47        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.23/0.47      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.23/0.47  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('63', plain,
% 0.23/0.47      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.23/0.47        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.23/0.47      inference('clc', [status(thm)], ['61', '62'])).
% 0.23/0.47  thf('64', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.23/0.47      inference('clc', [status(thm)], ['31', '32'])).
% 0.23/0.47  thf('65', plain,
% 0.23/0.47      ((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.23/0.47      inference('clc', [status(thm)], ['63', '64'])).
% 0.23/0.47  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 0.23/0.47  
% 0.23/0.47  % SZS output end Refutation
% 0.23/0.47  
% 0.23/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
