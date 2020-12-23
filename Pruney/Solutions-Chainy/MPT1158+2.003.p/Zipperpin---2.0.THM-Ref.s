%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1w3Ww2u9T1

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:58 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  194 (1583 expanded)
%              Number of leaves         :   29 ( 462 expanded)
%              Depth                    :   37
%              Number of atoms          : 2062 (31133 expanded)
%              Number of equality atoms :   37 ( 168 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ X14 @ ( a_2_1_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( X14 != X15 )
      | ( r2_hidden @ ( sk_E @ X15 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('10',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_E @ X15 @ X12 @ X11 ) @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_struct_0 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
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
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k2_orders_2 @ X10 @ X9 )
        = ( a_2_1_orders_2 @ X10 @ X9 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
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
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X11: $i,X12: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_E @ X15 @ X12 @ X11 ) @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_struct_0 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k2_orders_2 @ X10 @ X9 )
        = ( a_2_1_orders_2 @ X10 @ X9 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('63',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('64',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('68',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r2_orders_2 @ X11 @ ( sk_D @ X12 @ X11 @ X14 ) @ X13 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( a_2_1_orders_2 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72','73'])).

thf('75',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','76'])).

thf('78',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['65'])).

thf('79',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('80',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X14
        = ( sk_D @ X12 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( a_2_1_orders_2 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ( X0
        = ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ( X0
        = ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
      | ( X0
        = ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_B
      = ( sk_D @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['78','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['77','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','92'])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['61','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['28'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('102',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','104'])).

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

thf('106',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ ( k2_orders_2 @ X21 @ ( k6_domain_1 @ ( u1_struct_0 @ X21 ) @ X20 ) ) )
      | ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t50_orders_2])).

thf('107',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['107','108','109','110','111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','115'])).

thf('117',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['29','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['27','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('122',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('125',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('126',plain,(
    r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('127',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A ) @ ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['124','127'])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A ) @ ( k1_tarski @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('131',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('134',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('135',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ X14 @ ( a_2_1_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( X14 != X15 )
      | ~ ( r2_orders_2 @ X11 @ X15 @ ( sk_E @ X15 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('137',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( r2_orders_2 @ X11 @ X15 @ ( sk_E @ X15 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_struct_0 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('139',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C_1 ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','143'])).

thf('145',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['65'])).

thf('146',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['65'])).

thf('147',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['30','115','146'])).

thf('148',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['145','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','148','149'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('155',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('156',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['28'])).

thf('158',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','115'])).

thf('160',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['158','159'])).

thf('161',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['153','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['123','161'])).

thf('163',plain,(
    $false ),
    inference('sup-',[status(thm)],['120','162'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1w3Ww2u9T1
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:58:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.76  % Solved by: fo/fo7.sh
% 0.53/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.76  % done 609 iterations in 0.310s
% 0.53/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.76  % SZS output start Refutation
% 0.53/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.76  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.53/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.76  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.53/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.76  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.53/0.76  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.53/0.76  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.53/0.76  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.53/0.76  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.53/0.76  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.53/0.76  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.53/0.76  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.53/0.76  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.53/0.76  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.53/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.53/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.76  thf(t52_orders_2, conjecture,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.76         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.53/0.76       ( ![B:$i]:
% 0.53/0.76         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.76           ( ![C:$i]:
% 0.53/0.76             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.76               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.53/0.76                 ( r2_hidden @
% 0.53/0.76                   B @ 
% 0.53/0.76                   ( k2_orders_2 @
% 0.53/0.76                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.53/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.76    (~( ![A:$i]:
% 0.53/0.76        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.76            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.53/0.76          ( ![B:$i]:
% 0.53/0.76            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.76              ( ![C:$i]:
% 0.53/0.76                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.76                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.53/0.76                    ( r2_hidden @
% 0.53/0.76                      B @ 
% 0.53/0.76                      ( k2_orders_2 @
% 0.53/0.76                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.53/0.76    inference('cnf.neg', [status(esa)], [t52_orders_2])).
% 0.53/0.76  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf(t35_orders_2, axiom,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.53/0.76       ( ![B:$i]:
% 0.53/0.76         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.76           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.53/0.76             ( m1_subset_1 @
% 0.53/0.76               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.53/0.76               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.53/0.76  thf('2', plain,
% 0.53/0.76      (![X18 : $i, X19 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.53/0.76          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X19) @ X18) @ 
% 0.53/0.76             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.53/0.76          | ~ (l1_orders_2 @ X19)
% 0.53/0.76          | ~ (v3_orders_2 @ X19)
% 0.53/0.76          | (v2_struct_0 @ X19))),
% 0.53/0.76      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.53/0.76  thf('3', plain,
% 0.53/0.76      (((v2_struct_0 @ sk_A)
% 0.53/0.76        | ~ (v3_orders_2 @ sk_A)
% 0.53/0.76        | ~ (l1_orders_2 @ sk_A)
% 0.53/0.76        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.53/0.76           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.76  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('6', plain,
% 0.53/0.76      (((v2_struct_0 @ sk_A)
% 0.53/0.76        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.53/0.76           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.76      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.53/0.76  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('8', plain,
% 0.53/0.76      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.53/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.76      inference('clc', [status(thm)], ['6', '7'])).
% 0.53/0.76  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.53/0.76    (![A:$i,B:$i,C:$i]:
% 0.53/0.76     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.53/0.76         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.53/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.53/0.76       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.53/0.76         ( ?[D:$i]:
% 0.53/0.76           ( ( ![E:$i]:
% 0.53/0.76               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.53/0.76                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.53/0.76             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.53/0.76  thf('9', plain,
% 0.53/0.76      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.53/0.76         (~ (l1_orders_2 @ X11)
% 0.53/0.76          | ~ (v5_orders_2 @ X11)
% 0.53/0.76          | ~ (v4_orders_2 @ X11)
% 0.53/0.76          | ~ (v3_orders_2 @ X11)
% 0.53/0.76          | (v2_struct_0 @ X11)
% 0.53/0.76          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.53/0.76          | (r2_hidden @ X14 @ (a_2_1_orders_2 @ X11 @ X12))
% 0.53/0.76          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.53/0.76          | ((X14) != (X15))
% 0.53/0.76          | (r2_hidden @ (sk_E @ X15 @ X12 @ X11) @ X12))),
% 0.53/0.76      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.53/0.76  thf('10', plain,
% 0.53/0.76      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.53/0.76         ((r2_hidden @ (sk_E @ X15 @ X12 @ X11) @ X12)
% 0.53/0.76          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.53/0.76          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X11 @ X12))
% 0.53/0.76          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.53/0.76          | (v2_struct_0 @ X11)
% 0.53/0.76          | ~ (v3_orders_2 @ X11)
% 0.53/0.76          | ~ (v4_orders_2 @ X11)
% 0.53/0.76          | ~ (v5_orders_2 @ X11)
% 0.53/0.76          | ~ (l1_orders_2 @ X11))),
% 0.53/0.76      inference('simplify', [status(thm)], ['9'])).
% 0.53/0.76  thf('11', plain,
% 0.53/0.76      (![X0 : $i]:
% 0.53/0.76         (~ (l1_orders_2 @ sk_A)
% 0.53/0.76          | ~ (v5_orders_2 @ sk_A)
% 0.53/0.76          | ~ (v4_orders_2 @ sk_A)
% 0.53/0.76          | ~ (v3_orders_2 @ sk_A)
% 0.53/0.76          | (v2_struct_0 @ sk_A)
% 0.53/0.76          | (r2_hidden @ X0 @ 
% 0.53/0.76             (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.76              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.76          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.76          | (r2_hidden @ 
% 0.53/0.76             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.53/0.76             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.53/0.76      inference('sup-', [status(thm)], ['8', '10'])).
% 0.53/0.76  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('13', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.76  thf('16', plain,
% 0.53/0.76      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.53/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.76      inference('clc', [status(thm)], ['6', '7'])).
% 0.53/0.76  thf(d13_orders_2, axiom,
% 0.53/0.76    (![A:$i]:
% 0.53/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.76         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.53/0.76       ( ![B:$i]:
% 0.53/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.76           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.53/0.76  thf('17', plain,
% 0.53/0.76      (![X9 : $i, X10 : $i]:
% 0.53/0.76         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.53/0.76          | ((k2_orders_2 @ X10 @ X9) = (a_2_1_orders_2 @ X10 @ X9))
% 0.53/0.76          | ~ (l1_orders_2 @ X10)
% 0.53/0.76          | ~ (v5_orders_2 @ X10)
% 0.53/0.76          | ~ (v4_orders_2 @ X10)
% 0.53/0.76          | ~ (v3_orders_2 @ X10)
% 0.53/0.76          | (v2_struct_0 @ X10))),
% 0.53/0.76      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.53/0.76  thf('18', plain,
% 0.53/0.76      (((v2_struct_0 @ sk_A)
% 0.53/0.76        | ~ (v3_orders_2 @ sk_A)
% 0.53/0.76        | ~ (v4_orders_2 @ sk_A)
% 0.53/0.76        | ~ (v5_orders_2 @ sk_A)
% 0.53/0.76        | ~ (l1_orders_2 @ sk_A)
% 0.53/0.76        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77            = (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.53/0.77  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('23', plain,
% 0.53/0.77      (((v2_struct_0 @ sk_A)
% 0.53/0.77        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77            = (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.53/0.77      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.53/0.77  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('25', plain,
% 0.53/0.77      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77         = (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.53/0.77      inference('clc', [status(thm)], ['23', '24'])).
% 0.53/0.77  thf('26', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_A)
% 0.53/0.77          | (r2_hidden @ X0 @ 
% 0.53/0.77             (k2_orders_2 @ sk_A @ 
% 0.53/0.77              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | (r2_hidden @ 
% 0.53/0.77             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.53/0.77             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.53/0.77      inference('demod', [status(thm)], ['11', '12', '13', '14', '15', '25'])).
% 0.53/0.77  thf('27', plain,
% 0.53/0.77      (((r2_hidden @ 
% 0.53/0.77         (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.53/0.77         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77        | (r2_hidden @ sk_B @ 
% 0.53/0.77           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.77        | (v2_struct_0 @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['0', '26'])).
% 0.53/0.77  thf('28', plain,
% 0.53/0.77      ((~ (r2_hidden @ sk_B @ 
% 0.53/0.77           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.77        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('29', plain,
% 0.53/0.77      ((~ (r2_hidden @ sk_B @ 
% 0.53/0.77           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.53/0.77         <= (~
% 0.53/0.77             ((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('split', [status(esa)], ['28'])).
% 0.53/0.77  thf('30', plain,
% 0.53/0.77      (~
% 0.53/0.77       ((r2_hidden @ sk_B @ 
% 0.53/0.77         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))) | 
% 0.53/0.77       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.53/0.77      inference('split', [status(esa)], ['28'])).
% 0.53/0.77  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('33', plain,
% 0.53/0.77      (![X18 : $i, X19 : $i]:
% 0.53/0.77         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.53/0.77          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X19) @ X18) @ 
% 0.53/0.77             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.53/0.77          | ~ (l1_orders_2 @ X19)
% 0.53/0.77          | ~ (v3_orders_2 @ X19)
% 0.53/0.77          | (v2_struct_0 @ X19))),
% 0.53/0.77      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.53/0.77  thf('34', plain,
% 0.53/0.77      (((v2_struct_0 @ sk_A)
% 0.53/0.77        | ~ (v3_orders_2 @ sk_A)
% 0.53/0.77        | ~ (l1_orders_2 @ sk_A)
% 0.53/0.77        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.53/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['32', '33'])).
% 0.53/0.77  thf('35', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('37', plain,
% 0.53/0.77      (((v2_struct_0 @ sk_A)
% 0.53/0.77        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.53/0.77           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.77      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.53/0.77  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('39', plain,
% 0.53/0.77      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.53/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('clc', [status(thm)], ['37', '38'])).
% 0.53/0.77  thf('40', plain,
% 0.53/0.77      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.53/0.77         ((r2_hidden @ (sk_E @ X15 @ X12 @ X11) @ X12)
% 0.53/0.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.53/0.77          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X11 @ X12))
% 0.53/0.77          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.53/0.77          | (v2_struct_0 @ X11)
% 0.53/0.77          | ~ (v3_orders_2 @ X11)
% 0.53/0.77          | ~ (v4_orders_2 @ X11)
% 0.53/0.77          | ~ (v5_orders_2 @ X11)
% 0.53/0.77          | ~ (l1_orders_2 @ X11))),
% 0.53/0.77      inference('simplify', [status(thm)], ['9'])).
% 0.53/0.77  thf('41', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (l1_orders_2 @ sk_A)
% 0.53/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.53/0.77          | ~ (v4_orders_2 @ sk_A)
% 0.53/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | (r2_hidden @ X0 @ 
% 0.53/0.77             (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.53/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | (r2_hidden @ 
% 0.53/0.77             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.53/0.77             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.77  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('43', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('44', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('45', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('46', plain,
% 0.53/0.77      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.53/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('clc', [status(thm)], ['37', '38'])).
% 0.53/0.77  thf('47', plain,
% 0.53/0.77      (![X9 : $i, X10 : $i]:
% 0.53/0.77         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.53/0.77          | ((k2_orders_2 @ X10 @ X9) = (a_2_1_orders_2 @ X10 @ X9))
% 0.53/0.77          | ~ (l1_orders_2 @ X10)
% 0.53/0.77          | ~ (v5_orders_2 @ X10)
% 0.53/0.77          | ~ (v4_orders_2 @ X10)
% 0.53/0.77          | ~ (v3_orders_2 @ X10)
% 0.53/0.77          | (v2_struct_0 @ X10))),
% 0.53/0.77      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.53/0.77  thf('48', plain,
% 0.53/0.77      (((v2_struct_0 @ sk_A)
% 0.53/0.77        | ~ (v3_orders_2 @ sk_A)
% 0.53/0.77        | ~ (v4_orders_2 @ sk_A)
% 0.53/0.77        | ~ (v5_orders_2 @ sk_A)
% 0.53/0.77        | ~ (l1_orders_2 @ sk_A)
% 0.53/0.77        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.53/0.77            = (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['46', '47'])).
% 0.53/0.77  thf('49', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('50', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('51', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('52', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('53', plain,
% 0.53/0.77      (((v2_struct_0 @ sk_A)
% 0.53/0.77        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.53/0.77            = (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.53/0.77      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.53/0.77  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('55', plain,
% 0.53/0.77      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.53/0.77         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.53/0.77      inference('clc', [status(thm)], ['53', '54'])).
% 0.53/0.77  thf('56', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v2_struct_0 @ sk_A)
% 0.53/0.77          | (r2_hidden @ X0 @ 
% 0.53/0.77             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.53/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | (r2_hidden @ 
% 0.53/0.77             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.53/0.77             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.53/0.77      inference('demod', [status(thm)], ['41', '42', '43', '44', '45', '55'])).
% 0.53/0.77  thf('57', plain,
% 0.53/0.77      (((r2_hidden @ 
% 0.53/0.77         (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.53/0.77         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.53/0.77        | (r2_hidden @ sk_B @ 
% 0.53/0.77           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.53/0.77        | (v2_struct_0 @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['31', '56'])).
% 0.53/0.77  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('59', plain,
% 0.53/0.77      (((r2_hidden @ sk_B @ 
% 0.53/0.77         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.53/0.77        | (r2_hidden @ 
% 0.53/0.77           (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.53/0.77           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.53/0.77      inference('clc', [status(thm)], ['57', '58'])).
% 0.53/0.77  thf(d1_tarski, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.53/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.53/0.77  thf('60', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.77         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.53/0.77      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.77  thf('61', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.53/0.77      inference('simplify', [status(thm)], ['60'])).
% 0.53/0.77  thf('62', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(redefinition_k6_domain_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.53/0.77       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.53/0.77  thf('63', plain,
% 0.53/0.77      (![X16 : $i, X17 : $i]:
% 0.53/0.77         ((v1_xboole_0 @ X16)
% 0.53/0.77          | ~ (m1_subset_1 @ X17 @ X16)
% 0.53/0.77          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.53/0.77  thf('64', plain,
% 0.53/0.77      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.77  thf('65', plain,
% 0.53/0.77      (((r2_hidden @ sk_B @ 
% 0.53/0.77         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.77        | (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('66', plain,
% 0.53/0.77      (((r2_hidden @ sk_B @ 
% 0.53/0.77         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.53/0.77         <= (((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('split', [status(esa)], ['65'])).
% 0.53/0.77  thf('67', plain,
% 0.53/0.77      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.53/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('clc', [status(thm)], ['6', '7'])).
% 0.53/0.77  thf('68', plain,
% 0.53/0.77      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.53/0.77         (~ (l1_orders_2 @ X11)
% 0.53/0.77          | ~ (v5_orders_2 @ X11)
% 0.53/0.77          | ~ (v4_orders_2 @ X11)
% 0.53/0.77          | ~ (v3_orders_2 @ X11)
% 0.53/0.77          | (v2_struct_0 @ X11)
% 0.53/0.77          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.53/0.77          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.53/0.77          | (r2_orders_2 @ X11 @ (sk_D @ X12 @ X11 @ X14) @ X13)
% 0.53/0.77          | ~ (r2_hidden @ X13 @ X12)
% 0.53/0.77          | ~ (r2_hidden @ X14 @ (a_2_1_orders_2 @ X11 @ X12)))),
% 0.53/0.77      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.53/0.77  thf('69', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X0 @ 
% 0.53/0.77             (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.77          | ~ (r2_hidden @ X1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77          | (r2_orders_2 @ sk_A @ 
% 0.53/0.77             (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ X0) @ 
% 0.53/0.77             X1)
% 0.53/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.53/0.77          | ~ (v4_orders_2 @ sk_A)
% 0.53/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.53/0.77          | ~ (l1_orders_2 @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['67', '68'])).
% 0.53/0.77  thf('70', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('71', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('72', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('73', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('74', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X0 @ 
% 0.53/0.77             (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.77          | ~ (r2_hidden @ X1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77          | (r2_orders_2 @ sk_A @ 
% 0.53/0.77             (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ X0) @ 
% 0.53/0.77             X1)
% 0.53/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | (v2_struct_0 @ sk_A))),
% 0.53/0.77      inference('demod', [status(thm)], ['69', '70', '71', '72', '73'])).
% 0.53/0.77  thf('75', plain,
% 0.53/0.77      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77         = (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.53/0.77      inference('clc', [status(thm)], ['23', '24'])).
% 0.53/0.77  thf('76', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X0 @ 
% 0.53/0.77             (k2_orders_2 @ sk_A @ 
% 0.53/0.77              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.77          | ~ (r2_hidden @ X1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77          | (r2_orders_2 @ sk_A @ 
% 0.53/0.77             (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ X0) @ 
% 0.53/0.77             X1)
% 0.53/0.77          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | (v2_struct_0 @ sk_A))),
% 0.53/0.77      inference('demod', [status(thm)], ['74', '75'])).
% 0.53/0.77  thf('77', plain,
% 0.53/0.77      ((![X0 : $i]:
% 0.53/0.77          ((v2_struct_0 @ sk_A)
% 0.53/0.77           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77           | (r2_orders_2 @ sk_A @ 
% 0.53/0.77              (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ 
% 0.53/0.77               sk_B) @ 
% 0.53/0.77              X0)
% 0.53/0.77           | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.53/0.77         <= (((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['66', '76'])).
% 0.53/0.77  thf('78', plain,
% 0.53/0.77      (((r2_hidden @ sk_B @ 
% 0.53/0.77         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.53/0.77         <= (((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('split', [status(esa)], ['65'])).
% 0.53/0.77  thf('79', plain,
% 0.53/0.77      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.53/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('clc', [status(thm)], ['6', '7'])).
% 0.53/0.77  thf('80', plain,
% 0.53/0.77      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.53/0.77         (~ (l1_orders_2 @ X11)
% 0.53/0.77          | ~ (v5_orders_2 @ X11)
% 0.53/0.77          | ~ (v4_orders_2 @ X11)
% 0.53/0.77          | ~ (v3_orders_2 @ X11)
% 0.53/0.77          | (v2_struct_0 @ X11)
% 0.53/0.77          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.53/0.77          | ((X14) = (sk_D @ X12 @ X11 @ X14))
% 0.53/0.77          | ~ (r2_hidden @ X14 @ (a_2_1_orders_2 @ X11 @ X12)))),
% 0.53/0.77      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.53/0.77  thf('81', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X0 @ 
% 0.53/0.77             (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.77          | ((X0)
% 0.53/0.77              = (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ 
% 0.53/0.77                 X0))
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.53/0.77          | ~ (v4_orders_2 @ sk_A)
% 0.53/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.53/0.77          | ~ (l1_orders_2 @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['79', '80'])).
% 0.53/0.77  thf('82', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('83', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('84', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('85', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('86', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X0 @ 
% 0.53/0.77             (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.77          | ((X0)
% 0.53/0.77              = (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ 
% 0.53/0.77                 X0))
% 0.53/0.77          | (v2_struct_0 @ sk_A))),
% 0.53/0.77      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.53/0.77  thf('87', plain,
% 0.53/0.77      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77         = (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.53/0.77      inference('clc', [status(thm)], ['23', '24'])).
% 0.53/0.77  thf('88', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X0 @ 
% 0.53/0.77             (k2_orders_2 @ sk_A @ 
% 0.53/0.77              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.53/0.77          | ((X0)
% 0.53/0.77              = (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ 
% 0.53/0.77                 X0))
% 0.53/0.77          | (v2_struct_0 @ sk_A))),
% 0.53/0.77      inference('demod', [status(thm)], ['86', '87'])).
% 0.53/0.77  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('90', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (((X0)
% 0.53/0.77            = (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ X0))
% 0.53/0.77          | ~ (r2_hidden @ X0 @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.53/0.77      inference('clc', [status(thm)], ['88', '89'])).
% 0.53/0.77  thf('91', plain,
% 0.53/0.77      ((((sk_B)
% 0.53/0.77          = (sk_D @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A @ sk_B)))
% 0.53/0.77         <= (((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['78', '90'])).
% 0.53/0.77  thf('92', plain,
% 0.53/0.77      ((![X0 : $i]:
% 0.53/0.77          ((v2_struct_0 @ sk_A)
% 0.53/0.77           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77           | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.53/0.77           | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.53/0.77         <= (((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('demod', [status(thm)], ['77', '91'])).
% 0.53/0.77  thf('93', plain,
% 0.53/0.77      ((![X0 : $i]:
% 0.53/0.77          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.53/0.77           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77           | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.53/0.77           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77           | (v2_struct_0 @ sk_A)))
% 0.53/0.77         <= (((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['64', '92'])).
% 0.53/0.77  thf('94', plain,
% 0.53/0.77      ((((v2_struct_0 @ sk_A)
% 0.53/0.77         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.53/0.77         | (r2_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.53/0.77         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.53/0.77         <= (((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['61', '93'])).
% 0.53/0.77  thf('95', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('96', plain,
% 0.53/0.77      ((((v2_struct_0 @ sk_A)
% 0.53/0.77         | (r2_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.53/0.77         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.53/0.77         <= (((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('demod', [status(thm)], ['94', '95'])).
% 0.53/0.77  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('98', plain,
% 0.53/0.77      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77         | (r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))
% 0.53/0.77         <= (((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('clc', [status(thm)], ['96', '97'])).
% 0.53/0.77  thf('99', plain,
% 0.53/0.77      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.53/0.77         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.53/0.77      inference('split', [status(esa)], ['28'])).
% 0.53/0.77  thf('100', plain,
% 0.53/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.53/0.77         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.53/0.77             ((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['98', '99'])).
% 0.53/0.77  thf('101', plain,
% 0.53/0.77      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.53/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('clc', [status(thm)], ['37', '38'])).
% 0.53/0.77  thf(t5_subset, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.53/0.77          ( v1_xboole_0 @ C ) ) ))).
% 0.53/0.77  thf('102', plain,
% 0.53/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X6 @ X7)
% 0.53/0.77          | ~ (v1_xboole_0 @ X8)
% 0.53/0.77          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.53/0.77      inference('cnf', [status(esa)], [t5_subset])).
% 0.53/0.77  thf('103', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['101', '102'])).
% 0.53/0.77  thf('104', plain,
% 0.53/0.77      ((![X0 : $i]:
% 0.53/0.77          ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.53/0.77         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.53/0.77             ((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['100', '103'])).
% 0.53/0.77  thf('105', plain,
% 0.53/0.77      (((r2_hidden @ sk_B @ 
% 0.53/0.77         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.53/0.77         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.53/0.77             ((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['59', '104'])).
% 0.53/0.77  thf(t50_orders_2, axiom,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.53/0.77         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.53/0.77       ( ![B:$i]:
% 0.53/0.77         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.77           ( ~( r2_hidden @
% 0.53/0.77                B @ 
% 0.53/0.77                ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.53/0.77  thf('106', plain,
% 0.53/0.77      (![X20 : $i, X21 : $i]:
% 0.53/0.77         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.53/0.77          | ~ (r2_hidden @ X20 @ 
% 0.53/0.77               (k2_orders_2 @ X21 @ (k6_domain_1 @ (u1_struct_0 @ X21) @ X20)))
% 0.53/0.77          | ~ (l1_orders_2 @ X21)
% 0.53/0.77          | ~ (v5_orders_2 @ X21)
% 0.53/0.77          | ~ (v4_orders_2 @ X21)
% 0.53/0.77          | ~ (v3_orders_2 @ X21)
% 0.53/0.77          | (v2_struct_0 @ X21))),
% 0.53/0.77      inference('cnf', [status(esa)], [t50_orders_2])).
% 0.53/0.77  thf('107', plain,
% 0.53/0.77      ((((v2_struct_0 @ sk_A)
% 0.53/0.77         | ~ (v3_orders_2 @ sk_A)
% 0.53/0.77         | ~ (v4_orders_2 @ sk_A)
% 0.53/0.77         | ~ (v5_orders_2 @ sk_A)
% 0.53/0.77         | ~ (l1_orders_2 @ sk_A)
% 0.53/0.77         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.53/0.77         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.53/0.77             ((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['105', '106'])).
% 0.53/0.77  thf('108', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('109', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('110', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('111', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('112', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('113', plain,
% 0.53/0.77      (((v2_struct_0 @ sk_A))
% 0.53/0.77         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.53/0.77             ((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('demod', [status(thm)],
% 0.53/0.77                ['107', '108', '109', '110', '111', '112'])).
% 0.53/0.77  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('115', plain,
% 0.53/0.77      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.53/0.77       ~
% 0.53/0.77       ((r2_hidden @ sk_B @ 
% 0.53/0.77         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['113', '114'])).
% 0.53/0.77  thf('116', plain,
% 0.53/0.77      (~
% 0.53/0.77       ((r2_hidden @ sk_B @ 
% 0.53/0.77         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.53/0.77      inference('sat_resolution*', [status(thm)], ['30', '115'])).
% 0.53/0.77  thf('117', plain,
% 0.53/0.77      (~ (r2_hidden @ sk_B @ 
% 0.53/0.77          (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.53/0.77      inference('simpl_trail', [status(thm)], ['29', '116'])).
% 0.53/0.77  thf('118', plain,
% 0.53/0.77      (((v2_struct_0 @ sk_A)
% 0.53/0.77        | (r2_hidden @ 
% 0.53/0.77           (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.53/0.77           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.53/0.77      inference('clc', [status(thm)], ['27', '117'])).
% 0.53/0.77  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('120', plain,
% 0.53/0.77      ((r2_hidden @ 
% 0.53/0.77        (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.53/0.77        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.53/0.77      inference('clc', [status(thm)], ['118', '119'])).
% 0.53/0.77  thf('121', plain,
% 0.53/0.77      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.53/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('clc', [status(thm)], ['6', '7'])).
% 0.53/0.77  thf('122', plain,
% 0.53/0.77      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X6 @ X7)
% 0.53/0.77          | ~ (v1_xboole_0 @ X8)
% 0.53/0.77          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.53/0.77      inference('cnf', [status(esa)], [t5_subset])).
% 0.53/0.77  thf('123', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['121', '122'])).
% 0.53/0.77  thf('124', plain,
% 0.53/0.77      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.77  thf('125', plain,
% 0.53/0.77      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.77  thf('126', plain,
% 0.53/0.77      ((r2_hidden @ 
% 0.53/0.77        (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_A) @ 
% 0.53/0.77        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.53/0.77      inference('clc', [status(thm)], ['118', '119'])).
% 0.53/0.77  thf('127', plain,
% 0.53/0.77      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) @ 
% 0.53/0.77         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup+', [status(thm)], ['125', '126'])).
% 0.53/0.77  thf('128', plain,
% 0.53/0.77      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) @ 
% 0.53/0.77         (k1_tarski @ sk_C_1))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup+', [status(thm)], ['124', '127'])).
% 0.53/0.77  thf('129', plain,
% 0.53/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77        | (r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) @ 
% 0.53/0.77           (k1_tarski @ sk_C_1)))),
% 0.53/0.77      inference('simplify', [status(thm)], ['128'])).
% 0.53/0.77  thf('130', plain,
% 0.53/0.77      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.53/0.77      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.77  thf('131', plain,
% 0.53/0.77      (![X0 : $i, X3 : $i]:
% 0.53/0.77         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.53/0.77      inference('simplify', [status(thm)], ['130'])).
% 0.53/0.77  thf('132', plain,
% 0.53/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77        | ((sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) = (sk_C_1)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['129', '131'])).
% 0.53/0.77  thf('133', plain,
% 0.53/0.77      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.77  thf('134', plain,
% 0.53/0.77      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.53/0.77        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('clc', [status(thm)], ['6', '7'])).
% 0.53/0.77  thf('135', plain,
% 0.53/0.77      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.53/0.77         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup+', [status(thm)], ['133', '134'])).
% 0.53/0.77  thf('136', plain,
% 0.53/0.77      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.53/0.77         (~ (l1_orders_2 @ X11)
% 0.53/0.77          | ~ (v5_orders_2 @ X11)
% 0.53/0.77          | ~ (v4_orders_2 @ X11)
% 0.53/0.77          | ~ (v3_orders_2 @ X11)
% 0.53/0.77          | (v2_struct_0 @ X11)
% 0.53/0.77          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.53/0.77          | (r2_hidden @ X14 @ (a_2_1_orders_2 @ X11 @ X12))
% 0.53/0.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.53/0.77          | ((X14) != (X15))
% 0.53/0.77          | ~ (r2_orders_2 @ X11 @ X15 @ (sk_E @ X15 @ X12 @ X11)))),
% 0.53/0.77      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.53/0.77  thf('137', plain,
% 0.53/0.77      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.53/0.77         (~ (r2_orders_2 @ X11 @ X15 @ (sk_E @ X15 @ X12 @ X11))
% 0.53/0.77          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.53/0.77          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X11 @ X12))
% 0.53/0.77          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.53/0.77          | (v2_struct_0 @ X11)
% 0.53/0.77          | ~ (v3_orders_2 @ X11)
% 0.53/0.77          | ~ (v4_orders_2 @ X11)
% 0.53/0.77          | ~ (v5_orders_2 @ X11)
% 0.53/0.77          | ~ (l1_orders_2 @ X11))),
% 0.53/0.77      inference('simplify', [status(thm)], ['136'])).
% 0.53/0.77  thf('138', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | ~ (l1_orders_2 @ sk_A)
% 0.53/0.77          | ~ (v5_orders_2 @ sk_A)
% 0.53/0.77          | ~ (v4_orders_2 @ sk_A)
% 0.53/0.77          | ~ (v3_orders_2 @ sk_A)
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.53/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.53/0.77               (sk_E @ X0 @ (k1_tarski @ sk_C_1) @ sk_A)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['135', '137'])).
% 0.53/0.77  thf('139', plain, ((l1_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('140', plain, ((v5_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('141', plain, ((v4_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('142', plain, ((v3_orders_2 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('143', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | (v2_struct_0 @ sk_A)
% 0.53/0.77          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.53/0.77          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.53/0.77               (sk_E @ X0 @ (k1_tarski @ sk_C_1) @ sk_A)))),
% 0.53/0.77      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 0.53/0.77  thf('144', plain,
% 0.53/0.77      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.53/0.77        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.53/0.77        | (v2_struct_0 @ sk_A)
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['132', '143'])).
% 0.53/0.77  thf('145', plain,
% 0.53/0.77      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.53/0.77         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.53/0.77      inference('split', [status(esa)], ['65'])).
% 0.53/0.77  thf('146', plain,
% 0.53/0.77      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.53/0.77       ((r2_hidden @ sk_B @ 
% 0.53/0.77         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.53/0.77      inference('split', [status(esa)], ['65'])).
% 0.53/0.77  thf('147', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.53/0.77      inference('sat_resolution*', [status(thm)], ['30', '115', '146'])).
% 0.53/0.77  thf('148', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 0.53/0.77      inference('simpl_trail', [status(thm)], ['145', '147'])).
% 0.53/0.77  thf('149', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('150', plain,
% 0.53/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.53/0.77        | (v2_struct_0 @ sk_A)
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('demod', [status(thm)], ['144', '148', '149'])).
% 0.53/0.77  thf('151', plain,
% 0.53/0.77      (((v2_struct_0 @ sk_A)
% 0.53/0.77        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('simplify', [status(thm)], ['150'])).
% 0.53/0.77  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('153', plain,
% 0.53/0.77      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.53/0.77        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1))))),
% 0.53/0.77      inference('clc', [status(thm)], ['151', '152'])).
% 0.53/0.77  thf('154', plain,
% 0.53/0.77      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['62', '63'])).
% 0.53/0.77  thf('155', plain,
% 0.53/0.77      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77         = (a_2_1_orders_2 @ sk_A @ 
% 0.53/0.77            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))),
% 0.53/0.77      inference('clc', [status(thm)], ['23', '24'])).
% 0.53/0.77  thf('156', plain,
% 0.53/0.77      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.53/0.77          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('sup+', [status(thm)], ['154', '155'])).
% 0.53/0.77  thf('157', plain,
% 0.53/0.77      ((~ (r2_hidden @ sk_B @ 
% 0.53/0.77           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.53/0.77         <= (~
% 0.53/0.77             ((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('split', [status(esa)], ['28'])).
% 0.53/0.77  thf('158', plain,
% 0.53/0.77      (((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.53/0.77         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.53/0.77         <= (~
% 0.53/0.77             ((r2_hidden @ sk_B @ 
% 0.53/0.77               (k2_orders_2 @ sk_A @ 
% 0.53/0.77                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['156', '157'])).
% 0.53/0.77  thf('159', plain,
% 0.53/0.77      (~
% 0.53/0.77       ((r2_hidden @ sk_B @ 
% 0.53/0.77         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.53/0.77      inference('sat_resolution*', [status(thm)], ['30', '115'])).
% 0.53/0.77  thf('160', plain,
% 0.53/0.77      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.53/0.77        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.77      inference('simpl_trail', [status(thm)], ['158', '159'])).
% 0.53/0.77  thf('161', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.53/0.77      inference('clc', [status(thm)], ['153', '160'])).
% 0.53/0.77  thf('162', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 0.53/0.77      inference('demod', [status(thm)], ['123', '161'])).
% 0.53/0.77  thf('163', plain, ($false), inference('sup-', [status(thm)], ['120', '162'])).
% 0.53/0.77  
% 0.53/0.77  % SZS output end Refutation
% 0.53/0.77  
% 0.53/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
