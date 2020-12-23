%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.25IBrRuIWQ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:59 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  202 (1660 expanded)
%              Number of leaves         :   31 ( 484 expanded)
%              Depth                    :   38
%              Number of atoms          : 2124 (32150 expanded)
%              Number of equality atoms :   46 ( 216 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t52_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_orders_2 @ A @ B @ C )
                <=> ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_orders_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
            & ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(fraenkel_a_2_1_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v3_orders_2 @ B )
        & ( v4_orders_2 @ B )
        & ( v5_orders_2 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) )
      <=> ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
               => ( ( r2_hidden @ E @ C )
                 => ( r2_orders_2 @ B @ D @ E ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( X15 != X16 )
      | ( r2_hidden @ ( sk_E @ X16 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('10',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_E @ X16 @ X13 @ X12 ) @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(d13_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_orders_2 @ A @ B )
            = ( a_2_1_orders_2 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_orders_2 @ X11 @ X10 )
        = ( a_2_1_orders_2 @ X11 @ X10 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_E @ X16 @ X13 @ X12 ) @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_orders_2 @ X11 @ X10 )
        = ( a_2_1_orders_2 @ X11 @ X10 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45','55'])).

thf('57',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('62',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('66',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( X15
        = ( sk_D_1 @ X13 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('69',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B
      = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,
    ( ( ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['62','76'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('78',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('80',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','80'])).

thf('82',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('83',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('84',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('86',plain,
    ( ( ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('88',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('89',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r2_orders_2 @ X12 @ ( sk_D_1 @ X13 @ X12 @ X15 ) @ X14 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['86','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['81','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['77','103'])).

thf('105',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('109',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['59','111'])).

thf(t50_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('113',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_hidden @ X21 @ ( k2_orders_2 @ X22 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t50_orders_2])).

thf('114',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','122'])).

thf('124',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['29','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['27','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('129',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('132',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('133',plain,(
    r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('134',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['131','134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('138',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('139',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['137','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['136','141'])).

thf('143',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('144',plain,(
    ! [X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( X15 != X16 )
      | ~ ( r2_orders_2 @ X12 @ X16 @ ( sk_E @ X16 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('145',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ~ ( r2_orders_2 @ X12 @ X16 @ ( sk_E @ X16 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['143','145'])).

thf('147',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150'])).

thf('152',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','151'])).

thf('153',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['63'])).

thf('154',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('155',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['30','122','154'])).

thf('156',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['153','155'])).

thf('157',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['152','156','157'])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('163',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['28'])).

thf('164',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','122'])).

thf('166',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['164','165'])).

thf('167',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['161','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','167'])).

thf('169',plain,(
    $false ),
    inference('sup-',[status(thm)],['127','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.25IBrRuIWQ
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:41:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.78/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/0.96  % Solved by: fo/fo7.sh
% 0.78/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.96  % done 841 iterations in 0.494s
% 0.78/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/0.96  % SZS output start Refutation
% 0.78/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.96  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.78/0.96  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.78/0.96  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.78/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.78/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.78/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.78/0.96  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.78/0.96  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.78/0.96  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.78/0.96  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.78/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/0.96  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.78/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.78/0.96  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.78/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/0.96  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.78/0.96  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.78/0.96  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.78/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.96  thf(t52_orders_2, conjecture,
% 0.78/0.96    (![A:$i]:
% 0.78/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.78/0.96         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.78/0.96       ( ![B:$i]:
% 0.78/0.96         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.96           ( ![C:$i]:
% 0.78/0.96             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.96               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.78/0.96                 ( r2_hidden @
% 0.78/0.96                   B @ 
% 0.78/0.96                   ( k2_orders_2 @
% 0.78/0.96                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.78/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.96    (~( ![A:$i]:
% 0.78/0.96        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.78/0.96            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.78/0.96          ( ![B:$i]:
% 0.78/0.96            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.96              ( ![C:$i]:
% 0.78/0.96                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.96                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.78/0.96                    ( r2_hidden @
% 0.78/0.96                      B @ 
% 0.78/0.96                      ( k2_orders_2 @
% 0.78/0.96                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.78/0.96    inference('cnf.neg', [status(esa)], [t52_orders_2])).
% 0.78/0.96  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf(t35_orders_2, axiom,
% 0.78/0.96    (![A:$i]:
% 0.78/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.78/0.96       ( ![B:$i]:
% 0.78/0.96         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.96           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.78/0.96             ( m1_subset_1 @
% 0.78/0.96               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.78/0.96               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.78/0.96  thf('2', plain,
% 0.78/0.96      (![X19 : $i, X20 : $i]:
% 0.78/0.96         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.78/0.96          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X20) @ X19) @ 
% 0.78/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.78/0.96          | ~ (l1_orders_2 @ X20)
% 0.78/0.96          | ~ (v3_orders_2 @ X20)
% 0.78/0.96          | (v2_struct_0 @ X20))),
% 0.78/0.96      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.78/0.96  thf('3', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.78/0.96           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.78/0.96  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('6', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.78/0.96           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.78/0.96      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.78/0.96  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('8', plain,
% 0.78/0.96      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.78/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('clc', [status(thm)], ['6', '7'])).
% 0.78/0.96  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i]:
% 0.78/0.96     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.78/0.96         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.78/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.78/0.96       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.78/0.96         ( ?[D:$i]:
% 0.78/0.96           ( ( ![E:$i]:
% 0.78/0.96               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.78/0.96                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.78/0.96             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.78/0.96  thf('9', plain,
% 0.78/0.96      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.78/0.96         (~ (l1_orders_2 @ X12)
% 0.78/0.96          | ~ (v5_orders_2 @ X12)
% 0.78/0.96          | ~ (v4_orders_2 @ X12)
% 0.78/0.96          | ~ (v3_orders_2 @ X12)
% 0.78/0.96          | (v2_struct_0 @ X12)
% 0.78/0.96          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.78/0.96          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.78/0.96          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.78/0.96          | ((X15) != (X16))
% 0.78/0.96          | (r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13))),
% 0.78/0.96      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.78/0.96  thf('10', plain,
% 0.78/0.96      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.78/0.96         ((r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13)
% 0.78/0.96          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.78/0.96          | (r2_hidden @ X16 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.78/0.96          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.78/0.96          | (v2_struct_0 @ X12)
% 0.78/0.96          | ~ (v3_orders_2 @ X12)
% 0.78/0.96          | ~ (v4_orders_2 @ X12)
% 0.78/0.96          | ~ (v5_orders_2 @ X12)
% 0.78/0.96          | ~ (l1_orders_2 @ X12))),
% 0.78/0.96      inference('simplify', [status(thm)], ['9'])).
% 0.78/0.96  thf('11', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (l1_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (r2_hidden @ X0 @ 
% 0.78/0.96             (a_2_1_orders_2 @ sk_A @ 
% 0.78/0.96              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ 
% 0.78/0.96             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.78/0.96             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['8', '10'])).
% 0.78/0.96  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('13', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('16', plain,
% 0.78/0.96      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.78/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('clc', [status(thm)], ['6', '7'])).
% 0.78/0.96  thf(d13_orders_2, axiom,
% 0.78/0.96    (![A:$i]:
% 0.78/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.78/0.96         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.78/0.96       ( ![B:$i]:
% 0.78/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.78/0.96           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.78/0.96  thf('17', plain,
% 0.78/0.96      (![X10 : $i, X11 : $i]:
% 0.78/0.96         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.78/0.96          | ((k2_orders_2 @ X11 @ X10) = (a_2_1_orders_2 @ X11 @ X10))
% 0.78/0.96          | ~ (l1_orders_2 @ X11)
% 0.78/0.96          | ~ (v5_orders_2 @ X11)
% 0.78/0.96          | ~ (v4_orders_2 @ X11)
% 0.78/0.96          | ~ (v3_orders_2 @ X11)
% 0.78/0.96          | (v2_struct_0 @ X11))),
% 0.78/0.96      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.78/0.96  thf('18', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96        | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96        | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.78/0.96            = (a_2_1_orders_2 @ sk_A @ 
% 0.78/0.96               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['16', '17'])).
% 0.78/0.96  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('23', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.78/0.96            = (a_2_1_orders_2 @ sk_A @ 
% 0.78/0.96               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.78/0.96      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.78/0.96  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('25', plain,
% 0.78/0.96      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.78/0.96         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.78/0.96      inference('clc', [status(thm)], ['23', '24'])).
% 0.78/0.96  thf('26', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (r2_hidden @ X0 @ 
% 0.78/0.96             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ 
% 0.78/0.96             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.78/0.96             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.78/0.96      inference('demod', [status(thm)], ['11', '12', '13', '14', '15', '25'])).
% 0.78/0.96  thf('27', plain,
% 0.78/0.96      (((r2_hidden @ 
% 0.78/0.96         (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.78/0.96         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.78/0.96        | (r2_hidden @ sk_B @ 
% 0.78/0.96           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['0', '26'])).
% 0.78/0.96  thf('28', plain,
% 0.78/0.96      ((~ (r2_hidden @ sk_B @ 
% 0.78/0.96           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.78/0.96        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('29', plain,
% 0.78/0.96      ((~ (r2_hidden @ sk_B @ 
% 0.78/0.96           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('split', [status(esa)], ['28'])).
% 0.78/0.96  thf('30', plain,
% 0.78/0.96      (~
% 0.78/0.96       ((r2_hidden @ sk_B @ 
% 0.78/0.96         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 0.78/0.96       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.78/0.96      inference('split', [status(esa)], ['28'])).
% 0.78/0.96  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('33', plain,
% 0.78/0.96      (![X19 : $i, X20 : $i]:
% 0.78/0.96         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.78/0.96          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X20) @ X19) @ 
% 0.78/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.78/0.96          | ~ (l1_orders_2 @ X20)
% 0.78/0.96          | ~ (v3_orders_2 @ X20)
% 0.78/0.96          | (v2_struct_0 @ X20))),
% 0.78/0.96      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.78/0.96  thf('34', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.78/0.96           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['32', '33'])).
% 0.78/0.96  thf('35', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('37', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.78/0.96           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.78/0.96      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.78/0.96  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('39', plain,
% 0.78/0.96      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.78/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('clc', [status(thm)], ['37', '38'])).
% 0.78/0.96  thf('40', plain,
% 0.78/0.96      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.78/0.96         ((r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13)
% 0.78/0.96          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.78/0.96          | (r2_hidden @ X16 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.78/0.96          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.78/0.96          | (v2_struct_0 @ X12)
% 0.78/0.96          | ~ (v3_orders_2 @ X12)
% 0.78/0.96          | ~ (v4_orders_2 @ X12)
% 0.78/0.96          | ~ (v5_orders_2 @ X12)
% 0.78/0.96          | ~ (l1_orders_2 @ X12))),
% 0.78/0.96      inference('simplify', [status(thm)], ['9'])).
% 0.78/0.96  thf('41', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (l1_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (r2_hidden @ X0 @ 
% 0.78/0.96             (a_2_1_orders_2 @ sk_A @ 
% 0.78/0.96              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ 
% 0.78/0.96             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.78/0.96             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['39', '40'])).
% 0.78/0.96  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('43', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('44', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('45', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('46', plain,
% 0.78/0.96      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.78/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('clc', [status(thm)], ['37', '38'])).
% 0.78/0.96  thf('47', plain,
% 0.78/0.96      (![X10 : $i, X11 : $i]:
% 0.78/0.96         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.78/0.96          | ((k2_orders_2 @ X11 @ X10) = (a_2_1_orders_2 @ X11 @ X10))
% 0.78/0.96          | ~ (l1_orders_2 @ X11)
% 0.78/0.96          | ~ (v5_orders_2 @ X11)
% 0.78/0.96          | ~ (v4_orders_2 @ X11)
% 0.78/0.96          | ~ (v3_orders_2 @ X11)
% 0.78/0.96          | (v2_struct_0 @ X11))),
% 0.78/0.96      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.78/0.96  thf('48', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96        | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96        | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96        | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.78/0.96            = (a_2_1_orders_2 @ sk_A @ 
% 0.78/0.96               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['46', '47'])).
% 0.78/0.96  thf('49', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('50', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('51', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('52', plain, ((l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('53', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.78/0.96            = (a_2_1_orders_2 @ sk_A @ 
% 0.78/0.96               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.78/0.96      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.78/0.96  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('55', plain,
% 0.78/0.96      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.78/0.96         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.78/0.96      inference('clc', [status(thm)], ['53', '54'])).
% 0.78/0.96  thf('56', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v2_struct_0 @ sk_A)
% 0.78/0.96          | (r2_hidden @ X0 @ 
% 0.78/0.96             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (r2_hidden @ 
% 0.78/0.96             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.78/0.96             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.78/0.96      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '55'])).
% 0.78/0.96  thf('57', plain,
% 0.78/0.96      (((r2_hidden @ 
% 0.78/0.96         (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.78/0.96         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.78/0.96        | (r2_hidden @ sk_B @ 
% 0.78/0.96           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.78/0.96        | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['31', '56'])).
% 0.78/0.96  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('59', plain,
% 0.78/0.96      (((r2_hidden @ sk_B @ 
% 0.78/0.96         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.78/0.96        | (r2_hidden @ 
% 0.78/0.96           (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.78/0.96           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.78/0.96      inference('clc', [status(thm)], ['57', '58'])).
% 0.78/0.96  thf('60', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf(redefinition_k6_domain_1, axiom,
% 0.78/0.96    (![A:$i,B:$i]:
% 0.78/0.96     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.78/0.96       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.78/0.96  thf('61', plain,
% 0.78/0.96      (![X17 : $i, X18 : $i]:
% 0.78/0.96         ((v1_xboole_0 @ X17)
% 0.78/0.96          | ~ (m1_subset_1 @ X18 @ X17)
% 0.78/0.96          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.78/0.96      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.78/0.96  thf('62', plain,
% 0.78/0.96      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['60', '61'])).
% 0.78/0.96  thf('63', plain,
% 0.78/0.96      (((r2_hidden @ sk_B @ 
% 0.78/0.96         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.78/0.96        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('64', plain,
% 0.78/0.96      (((r2_hidden @ sk_B @ 
% 0.78/0.96         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('split', [status(esa)], ['63'])).
% 0.78/0.96  thf('65', plain,
% 0.78/0.96      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.78/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('clc', [status(thm)], ['6', '7'])).
% 0.78/0.96  thf('66', plain,
% 0.78/0.96      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.78/0.96         (~ (l1_orders_2 @ X12)
% 0.78/0.96          | ~ (v5_orders_2 @ X12)
% 0.78/0.96          | ~ (v4_orders_2 @ X12)
% 0.78/0.96          | ~ (v3_orders_2 @ X12)
% 0.78/0.96          | (v2_struct_0 @ X12)
% 0.78/0.96          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.78/0.96          | ((X15) = (sk_D_1 @ X13 @ X12 @ X15))
% 0.78/0.96          | ~ (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13)))),
% 0.78/0.96      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.78/0.96  thf('67', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (r2_hidden @ X0 @ 
% 0.78/0.96             (a_2_1_orders_2 @ sk_A @ 
% 0.78/0.96              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.78/0.96          | ((X0)
% 0.78/0.96              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ 
% 0.78/0.96                 X0))
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96          | ~ (l1_orders_2 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['65', '66'])).
% 0.78/0.96  thf('68', plain,
% 0.78/0.96      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.78/0.96         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.78/0.96      inference('clc', [status(thm)], ['23', '24'])).
% 0.78/0.96  thf('69', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('70', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('71', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('72', plain, ((l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('73', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (r2_hidden @ X0 @ 
% 0.78/0.96             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.78/0.96          | ((X0)
% 0.78/0.96              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ 
% 0.78/0.96                 X0))
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('demod', [status(thm)], ['67', '68', '69', '70', '71', '72'])).
% 0.78/0.96  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('75', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (((X0)
% 0.78/0.96            = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ X0))
% 0.78/0.96          | ~ (r2_hidden @ X0 @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.78/0.96      inference('clc', [status(thm)], ['73', '74'])).
% 0.78/0.96  thf('76', plain,
% 0.78/0.96      ((((sk_B)
% 0.78/0.96          = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ sk_B)))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['64', '75'])).
% 0.78/0.96  thf('77', plain,
% 0.78/0.96      (((((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))
% 0.78/0.96         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup+', [status(thm)], ['62', '76'])).
% 0.78/0.96  thf(t69_enumset1, axiom,
% 0.78/0.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.78/0.96  thf('78', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.78/0.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.78/0.96  thf(d2_tarski, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i]:
% 0.78/0.96     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.78/0.96       ( ![D:$i]:
% 0.78/0.96         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.78/0.96  thf('79', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.78/0.96         (((X1) != (X0))
% 0.78/0.96          | (r2_hidden @ X1 @ X2)
% 0.78/0.96          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.78/0.96      inference('cnf', [status(esa)], [d2_tarski])).
% 0.78/0.96  thf('80', plain,
% 0.78/0.96      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.78/0.96      inference('simplify', [status(thm)], ['79'])).
% 0.78/0.96  thf('81', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.78/0.96      inference('sup+', [status(thm)], ['78', '80'])).
% 0.78/0.96  thf('82', plain,
% 0.78/0.96      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['60', '61'])).
% 0.78/0.96  thf('83', plain,
% 0.78/0.96      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.78/0.96         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.78/0.96      inference('clc', [status(thm)], ['23', '24'])).
% 0.78/0.96  thf('84', plain,
% 0.78/0.96      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.78/0.96          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup+', [status(thm)], ['82', '83'])).
% 0.78/0.96  thf('85', plain,
% 0.78/0.96      (((r2_hidden @ sk_B @ 
% 0.78/0.96         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('split', [status(esa)], ['63'])).
% 0.78/0.96  thf('86', plain,
% 0.78/0.96      ((((r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup+', [status(thm)], ['84', '85'])).
% 0.78/0.96  thf('87', plain,
% 0.78/0.96      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['60', '61'])).
% 0.78/0.96  thf('88', plain,
% 0.78/0.96      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.78/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('clc', [status(thm)], ['6', '7'])).
% 0.78/0.96  thf('89', plain,
% 0.78/0.96      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.78/0.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup+', [status(thm)], ['87', '88'])).
% 0.78/0.96  thf('90', plain,
% 0.78/0.96      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.78/0.96         (~ (l1_orders_2 @ X12)
% 0.78/0.96          | ~ (v5_orders_2 @ X12)
% 0.78/0.96          | ~ (v4_orders_2 @ X12)
% 0.78/0.96          | ~ (v3_orders_2 @ X12)
% 0.78/0.96          | (v2_struct_0 @ X12)
% 0.78/0.96          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.78/0.96          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.78/0.96          | (r2_orders_2 @ X12 @ (sk_D_1 @ X13 @ X12 @ X15) @ X14)
% 0.78/0.96          | ~ (r2_hidden @ X14 @ X13)
% 0.78/0.96          | ~ (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13)))),
% 0.78/0.96      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.78/0.96  thf('91', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]:
% 0.78/0.96         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 0.78/0.96          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 0.78/0.96             X1)
% 0.78/0.96          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96          | ~ (l1_orders_2 @ sk_A))),
% 0.78/0.96      inference('sup-', [status(thm)], ['89', '90'])).
% 0.78/0.96  thf('92', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('93', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('94', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('96', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]:
% 0.78/0.96         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 0.78/0.96          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 0.78/0.96             X1)
% 0.78/0.96          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (v2_struct_0 @ sk_A))),
% 0.78/0.96      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.78/0.96  thf('97', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96           | (v2_struct_0 @ sk_A)
% 0.78/0.96           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96           | (r2_orders_2 @ sk_A @ 
% 0.78/0.96              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 0.78/0.96           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 0.78/0.96           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['86', '96'])).
% 0.78/0.96  thf('98', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 0.78/0.96           | (r2_orders_2 @ sk_A @ 
% 0.78/0.96              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 0.78/0.96           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96           | (v2_struct_0 @ sk_A)
% 0.78/0.96           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('simplify', [status(thm)], ['97'])).
% 0.78/0.96  thf('99', plain,
% 0.78/0.96      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.78/0.96            sk_C)))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['81', '98'])).
% 0.78/0.96  thf('100', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('101', plain,
% 0.78/0.96      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v2_struct_0 @ sk_A)
% 0.78/0.96         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.78/0.96            sk_C)))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('demod', [status(thm)], ['99', '100'])).
% 0.78/0.96  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('103', plain,
% 0.78/0.96      ((((r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.78/0.96          sk_C)
% 0.78/0.96         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('clc', [status(thm)], ['101', '102'])).
% 0.78/0.96  thf('104', plain,
% 0.78/0.96      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.78/0.96         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup+', [status(thm)], ['77', '103'])).
% 0.78/0.96  thf('105', plain,
% 0.78/0.96      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.78/0.96         <= (((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('simplify', [status(thm)], ['104'])).
% 0.78/0.96  thf('106', plain,
% 0.78/0.96      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.78/0.96         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.78/0.96      inference('split', [status(esa)], ['28'])).
% 0.78/0.96  thf('107', plain,
% 0.78/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.78/0.96         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.78/0.96             ((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['105', '106'])).
% 0.78/0.96  thf('108', plain,
% 0.78/0.96      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.78/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('clc', [status(thm)], ['37', '38'])).
% 0.78/0.96  thf(t5_subset, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i]:
% 0.78/0.96     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.78/0.96          ( v1_xboole_0 @ C ) ) ))).
% 0.78/0.96  thf('109', plain,
% 0.78/0.96      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.78/0.96         (~ (r2_hidden @ X7 @ X8)
% 0.78/0.96          | ~ (v1_xboole_0 @ X9)
% 0.78/0.96          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t5_subset])).
% 0.78/0.96  thf('110', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['108', '109'])).
% 0.78/0.96  thf('111', plain,
% 0.78/0.96      ((![X0 : $i]:
% 0.78/0.96          ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.78/0.96         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.78/0.96             ((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['107', '110'])).
% 0.78/0.96  thf('112', plain,
% 0.78/0.96      (((r2_hidden @ sk_B @ 
% 0.78/0.96         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.78/0.96         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.78/0.96             ((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['59', '111'])).
% 0.78/0.96  thf(t50_orders_2, axiom,
% 0.78/0.96    (![A:$i]:
% 0.78/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.78/0.96         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.78/0.96       ( ![B:$i]:
% 0.78/0.96         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.96           ( ~( r2_hidden @
% 0.78/0.96                B @ 
% 0.78/0.96                ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.78/0.96  thf('113', plain,
% 0.78/0.96      (![X21 : $i, X22 : $i]:
% 0.78/0.96         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.78/0.96          | ~ (r2_hidden @ X21 @ 
% 0.78/0.96               (k2_orders_2 @ X22 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21)))
% 0.78/0.96          | ~ (l1_orders_2 @ X22)
% 0.78/0.96          | ~ (v5_orders_2 @ X22)
% 0.78/0.96          | ~ (v4_orders_2 @ X22)
% 0.78/0.96          | ~ (v3_orders_2 @ X22)
% 0.78/0.96          | (v2_struct_0 @ X22))),
% 0.78/0.96      inference('cnf', [status(esa)], [t50_orders_2])).
% 0.78/0.96  thf('114', plain,
% 0.78/0.96      ((((v2_struct_0 @ sk_A)
% 0.78/0.96         | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96         | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96         | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96         | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.78/0.96             ((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['112', '113'])).
% 0.78/0.96  thf('115', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('116', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('117', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('118', plain, ((l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('119', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('120', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A))
% 0.78/0.96         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.78/0.96             ((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('demod', [status(thm)],
% 0.78/0.96                ['114', '115', '116', '117', '118', '119'])).
% 0.78/0.96  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('122', plain,
% 0.78/0.96      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.78/0.96       ~
% 0.78/0.96       ((r2_hidden @ sk_B @ 
% 0.78/0.96         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['120', '121'])).
% 0.78/0.96  thf('123', plain,
% 0.78/0.96      (~
% 0.78/0.96       ((r2_hidden @ sk_B @ 
% 0.78/0.96         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.78/0.96      inference('sat_resolution*', [status(thm)], ['30', '122'])).
% 0.78/0.96  thf('124', plain,
% 0.78/0.96      (~ (r2_hidden @ sk_B @ 
% 0.78/0.96          (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.78/0.96      inference('simpl_trail', [status(thm)], ['29', '123'])).
% 0.78/0.96  thf('125', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_hidden @ 
% 0.78/0.96           (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.78/0.96           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.78/0.96      inference('clc', [status(thm)], ['27', '124'])).
% 0.78/0.96  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('127', plain,
% 0.78/0.96      ((r2_hidden @ 
% 0.78/0.96        (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.78/0.96        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.78/0.96      inference('clc', [status(thm)], ['125', '126'])).
% 0.78/0.96  thf('128', plain,
% 0.78/0.96      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.78/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('clc', [status(thm)], ['6', '7'])).
% 0.78/0.96  thf('129', plain,
% 0.78/0.96      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.78/0.96         (~ (r2_hidden @ X7 @ X8)
% 0.78/0.96          | ~ (v1_xboole_0 @ X9)
% 0.78/0.96          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t5_subset])).
% 0.78/0.96  thf('130', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['128', '129'])).
% 0.78/0.96  thf('131', plain,
% 0.78/0.96      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['60', '61'])).
% 0.78/0.96  thf('132', plain,
% 0.78/0.96      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['60', '61'])).
% 0.78/0.96  thf('133', plain,
% 0.78/0.96      ((r2_hidden @ 
% 0.78/0.96        (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.78/0.96        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.78/0.96      inference('clc', [status(thm)], ['125', '126'])).
% 0.78/0.96  thf('134', plain,
% 0.78/0.96      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.78/0.96         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup+', [status(thm)], ['132', '133'])).
% 0.78/0.96  thf('135', plain,
% 0.78/0.96      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.78/0.96         (k1_tarski @ sk_C))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup+', [status(thm)], ['131', '134'])).
% 0.78/0.96  thf('136', plain,
% 0.78/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.78/0.96           (k1_tarski @ sk_C)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['135'])).
% 0.78/0.96  thf('137', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.78/0.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.78/0.96  thf('138', plain,
% 0.78/0.96      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.78/0.96         (~ (r2_hidden @ X4 @ X2)
% 0.78/0.96          | ((X4) = (X3))
% 0.78/0.96          | ((X4) = (X0))
% 0.78/0.96          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.78/0.96      inference('cnf', [status(esa)], [d2_tarski])).
% 0.78/0.96  thf('139', plain,
% 0.78/0.96      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.78/0.96         (((X4) = (X0))
% 0.78/0.96          | ((X4) = (X3))
% 0.78/0.96          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['138'])).
% 0.78/0.96  thf('140', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]:
% 0.78/0.96         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['137', '139'])).
% 0.78/0.96  thf('141', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]:
% 0.78/0.96         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['140'])).
% 0.78/0.96  thf('142', plain,
% 0.78/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['136', '141'])).
% 0.78/0.96  thf('143', plain,
% 0.78/0.96      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.78/0.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup+', [status(thm)], ['87', '88'])).
% 0.78/0.96  thf('144', plain,
% 0.78/0.96      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.78/0.96         (~ (l1_orders_2 @ X12)
% 0.78/0.96          | ~ (v5_orders_2 @ X12)
% 0.78/0.96          | ~ (v4_orders_2 @ X12)
% 0.78/0.96          | ~ (v3_orders_2 @ X12)
% 0.78/0.96          | (v2_struct_0 @ X12)
% 0.78/0.96          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.78/0.96          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.78/0.96          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.78/0.96          | ((X15) != (X16))
% 0.78/0.96          | ~ (r2_orders_2 @ X12 @ X16 @ (sk_E @ X16 @ X13 @ X12)))),
% 0.78/0.96      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.78/0.96  thf('145', plain,
% 0.78/0.96      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.78/0.96         (~ (r2_orders_2 @ X12 @ X16 @ (sk_E @ X16 @ X13 @ X12))
% 0.78/0.96          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.78/0.96          | (r2_hidden @ X16 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.78/0.96          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.78/0.96          | (v2_struct_0 @ X12)
% 0.78/0.96          | ~ (v3_orders_2 @ X12)
% 0.78/0.96          | ~ (v4_orders_2 @ X12)
% 0.78/0.96          | ~ (v5_orders_2 @ X12)
% 0.78/0.96          | ~ (l1_orders_2 @ X12))),
% 0.78/0.96      inference('simplify', [status(thm)], ['144'])).
% 0.78/0.96  thf('146', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (l1_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v5_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v4_orders_2 @ sk_A)
% 0.78/0.96          | ~ (v3_orders_2 @ sk_A)
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.78/0.96               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['143', '145'])).
% 0.78/0.96  thf('147', plain, ((l1_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('148', plain, ((v5_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('149', plain, ((v4_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('150', plain, ((v3_orders_2 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('151', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | (v2_struct_0 @ sk_A)
% 0.78/0.96          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.78/0.96               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 0.78/0.96      inference('demod', [status(thm)], ['146', '147', '148', '149', '150'])).
% 0.78/0.96  thf('152', plain,
% 0.78/0.96      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['142', '151'])).
% 0.78/0.96  thf('153', plain,
% 0.78/0.96      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.78/0.96         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.78/0.96      inference('split', [status(esa)], ['63'])).
% 0.78/0.96  thf('154', plain,
% 0.78/0.96      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.78/0.96       ((r2_hidden @ sk_B @ 
% 0.78/0.96         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.78/0.96      inference('split', [status(esa)], ['63'])).
% 0.78/0.96  thf('155', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.78/0.96      inference('sat_resolution*', [status(thm)], ['30', '122', '154'])).
% 0.78/0.96  thf('156', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.78/0.96      inference('simpl_trail', [status(thm)], ['153', '155'])).
% 0.78/0.96  thf('157', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('158', plain,
% 0.78/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96        | (v2_struct_0 @ sk_A)
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('demod', [status(thm)], ['152', '156', '157'])).
% 0.78/0.96  thf('159', plain,
% 0.78/0.96      (((v2_struct_0 @ sk_A)
% 0.78/0.96        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['158'])).
% 0.78/0.96  thf('160', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('161', plain,
% 0.78/0.96      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.96        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.78/0.96      inference('clc', [status(thm)], ['159', '160'])).
% 0.78/0.96  thf('162', plain,
% 0.78/0.96      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.78/0.96          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('sup+', [status(thm)], ['82', '83'])).
% 0.78/0.96  thf('163', plain,
% 0.78/0.96      ((~ (r2_hidden @ sk_B @ 
% 0.78/0.96           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('split', [status(esa)], ['28'])).
% 0.78/0.96  thf('164', plain,
% 0.78/0.96      (((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.96         <= (~
% 0.78/0.96             ((r2_hidden @ sk_B @ 
% 0.78/0.96               (k2_orders_2 @ sk_A @ 
% 0.78/0.96                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.78/0.96      inference('sup-', [status(thm)], ['162', '163'])).
% 0.78/0.96  thf('165', plain,
% 0.78/0.96      (~
% 0.78/0.96       ((r2_hidden @ sk_B @ 
% 0.78/0.96         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.78/0.96      inference('sat_resolution*', [status(thm)], ['30', '122'])).
% 0.78/0.96  thf('166', plain,
% 0.78/0.96      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.78/0.96        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.96      inference('simpl_trail', [status(thm)], ['164', '165'])).
% 0.78/0.96  thf('167', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.78/0.96      inference('clc', [status(thm)], ['161', '166'])).
% 0.78/0.96  thf('168', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.78/0.96      inference('demod', [status(thm)], ['130', '167'])).
% 0.78/0.96  thf('169', plain, ($false), inference('sup-', [status(thm)], ['127', '168'])).
% 0.78/0.96  
% 0.78/0.96  % SZS output end Refutation
% 0.78/0.96  
% 0.78/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
