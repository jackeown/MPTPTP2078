%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RUE4UuC3Og

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:59 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  210 (1547 expanded)
%              Number of leaves         :   47 ( 459 expanded)
%              Depth                    :   35
%              Number of atoms          : 2120 (28510 expanded)
%              Number of equality atoms :   42 ( 188 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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

thf(t24_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ B ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r1_orders_2 @ X20 @ X19 @ X19 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['36','37'])).

thf(t38_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v3_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ~ ( ! [D: $i] :
                        ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                          & ( v6_orders_2 @ D @ A ) )
                       => ~ ( ( r2_hidden @ C @ D )
                            & ( r2_hidden @ B @ D ) ) )
                    & ( ( r1_orders_2 @ A @ C @ B )
                      | ( r1_orders_2 @ A @ B @ C ) ) )
                & ~ ( ~ ( r1_orders_2 @ A @ C @ B )
                    & ~ ( r1_orders_2 @ A @ B @ C )
                    & ? [D: $i] :
                        ( ( v6_orders_2 @ D @ A )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ B @ D )
                        & ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( ( r1_orders_2 @ A @ B @ C )
        | ( r1_orders_2 @ A @ C @ B ) )
     => ( zip_tseitin_3 @ C @ B @ A ) ) )).

thf('39',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_3 @ X32 @ X33 @ X34 )
      | ~ ( r1_orders_2 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('40',plain,(
    zip_tseitin_3 @ sk_B @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ D @ A )
       => ~ ( zip_tseitin_1 @ D @ C @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_2 @ X28 @ X29 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B )
     => ( ( r2_hidden @ B @ D )
        & ( r2_hidden @ C @ D ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [D: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ A )
     => ( ( v6_orders_2 @ D @ A )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_9,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ~ ( ? [D: $i] :
                        ( ( r2_hidden @ C @ D )
                        & ( r2_hidden @ B @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( v6_orders_2 @ D @ A ) )
                    & ~ ( r1_orders_2 @ A @ B @ C )
                    & ~ ( r1_orders_2 @ A @ C @ B ) )
                & ~ ( ( zip_tseitin_3 @ C @ B @ A )
                    & ! [D: $i] :
                        ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X37 @ X35 @ X36 ) @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_3 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    zip_tseitin_1 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X26 @ X27 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('53',plain,(
    r2_hidden @ sk_B @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('55',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('56',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('60',plain,(
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

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('63',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B
      = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf('71',plain,
    ( ( ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['56','70'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('72',plain,(
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

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('74',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','74'])).

thf('76',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('77',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('78',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['57'])).

thf('80',plain,
    ( ( ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('82',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('83',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
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

thf('85',plain,(
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
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['75','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['71','97'])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    zip_tseitin_3 @ sk_B @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['38','39'])).

thf('103',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_2 @ X28 @ X29 @ X30 @ X31 )
      | ( zip_tseitin_0 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    zip_tseitin_0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( zip_tseitin_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('110',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('111',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['101','112'])).

thf('114',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['53','113'])).

thf('115',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','114'])).

thf('116',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['29','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['27','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('121',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('124',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('125',plain,(
    r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('126',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('130',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('131',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['128','133'])).

thf('135',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('136',plain,(
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

thf('137',plain,(
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
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
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
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142'])).

thf('144',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['57'])).

thf('146',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['57'])).

thf('147',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['30','114','146'])).

thf('148',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['145','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['144','148','149'])).

thf('151',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('155',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['28'])).

thf('156',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','114'])).

thf('158',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['156','157'])).

thf('159',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['153','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','159'])).

thf('161',plain,(
    $false ),
    inference('sup-',[status(thm)],['119','160'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RUE4UuC3Og
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:17:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.71/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.88  % Solved by: fo/fo7.sh
% 0.71/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.88  % done 709 iterations in 0.434s
% 0.71/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.88  % SZS output start Refutation
% 0.71/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.88  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.71/0.88  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.71/0.88  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.71/0.88  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.71/0.88  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.71/0.88  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.71/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.71/0.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.71/0.88  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.88  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.71/0.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.71/0.88  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.71/0.88  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.71/0.88  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.71/0.88  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.71/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.71/0.88  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.71/0.88  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.71/0.88  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.71/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.71/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.88  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.71/0.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.71/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.88  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.71/0.88  thf(t52_orders_2, conjecture,
% 0.71/0.88    (![A:$i]:
% 0.71/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.71/0.88         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.71/0.88       ( ![B:$i]:
% 0.71/0.88         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.88           ( ![C:$i]:
% 0.71/0.88             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.88               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.71/0.88                 ( r2_hidden @
% 0.71/0.88                   B @ 
% 0.71/0.88                   ( k2_orders_2 @
% 0.71/0.88                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.71/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.88    (~( ![A:$i]:
% 0.71/0.88        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.71/0.88            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.71/0.88          ( ![B:$i]:
% 0.71/0.88            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.88              ( ![C:$i]:
% 0.71/0.88                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.88                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.71/0.88                    ( r2_hidden @
% 0.71/0.88                      B @ 
% 0.71/0.88                      ( k2_orders_2 @
% 0.71/0.88                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.71/0.88    inference('cnf.neg', [status(esa)], [t52_orders_2])).
% 0.71/0.88  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf(t35_orders_2, axiom,
% 0.71/0.88    (![A:$i]:
% 0.71/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.71/0.88       ( ![B:$i]:
% 0.71/0.88         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.88           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.71/0.88             ( m1_subset_1 @
% 0.71/0.88               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.71/0.88               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.71/0.88  thf('2', plain,
% 0.71/0.88      (![X21 : $i, X22 : $i]:
% 0.71/0.88         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.71/0.88          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21) @ 
% 0.71/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.71/0.88          | ~ (l1_orders_2 @ X22)
% 0.71/0.88          | ~ (v3_orders_2 @ X22)
% 0.71/0.88          | (v2_struct_0 @ X22))),
% 0.71/0.88      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.71/0.88  thf('3', plain,
% 0.71/0.88      (((v2_struct_0 @ sk_A)
% 0.71/0.88        | ~ (v3_orders_2 @ sk_A)
% 0.71/0.88        | ~ (l1_orders_2 @ sk_A)
% 0.71/0.88        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.71/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.71/0.88  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('6', plain,
% 0.71/0.88      (((v2_struct_0 @ sk_A)
% 0.71/0.88        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.71/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.88      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.71/0.88  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('8', plain,
% 0.71/0.88      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.71/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.88      inference('clc', [status(thm)], ['6', '7'])).
% 0.71/0.88  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.71/0.88    (![A:$i,B:$i,C:$i]:
% 0.71/0.88     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.71/0.88         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.71/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.71/0.88       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.71/0.88         ( ?[D:$i]:
% 0.71/0.88           ( ( ![E:$i]:
% 0.71/0.88               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.71/0.88                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.71/0.88             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.71/0.88  thf('9', plain,
% 0.71/0.88      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.71/0.88         (~ (l1_orders_2 @ X12)
% 0.71/0.88          | ~ (v5_orders_2 @ X12)
% 0.71/0.88          | ~ (v4_orders_2 @ X12)
% 0.71/0.88          | ~ (v3_orders_2 @ X12)
% 0.71/0.88          | (v2_struct_0 @ X12)
% 0.71/0.88          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.71/0.88          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.71/0.88          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.71/0.88          | ((X15) != (X16))
% 0.71/0.88          | (r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13))),
% 0.71/0.88      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.71/0.88  thf('10', plain,
% 0.71/0.88      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.71/0.88         ((r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13)
% 0.71/0.88          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.71/0.88          | (r2_hidden @ X16 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.71/0.88          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.71/0.88          | (v2_struct_0 @ X12)
% 0.71/0.88          | ~ (v3_orders_2 @ X12)
% 0.71/0.88          | ~ (v4_orders_2 @ X12)
% 0.71/0.88          | ~ (v5_orders_2 @ X12)
% 0.71/0.88          | ~ (l1_orders_2 @ X12))),
% 0.71/0.88      inference('simplify', [status(thm)], ['9'])).
% 0.71/0.88  thf('11', plain,
% 0.71/0.88      (![X0 : $i]:
% 0.71/0.88         (~ (l1_orders_2 @ sk_A)
% 0.71/0.88          | ~ (v5_orders_2 @ sk_A)
% 0.71/0.88          | ~ (v4_orders_2 @ sk_A)
% 0.71/0.88          | ~ (v3_orders_2 @ sk_A)
% 0.71/0.88          | (v2_struct_0 @ sk_A)
% 0.71/0.88          | (r2_hidden @ X0 @ 
% 0.71/0.88             (a_2_1_orders_2 @ sk_A @ 
% 0.71/0.88              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.71/0.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.88          | (r2_hidden @ 
% 0.71/0.88             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.71/0.88             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.71/0.88      inference('sup-', [status(thm)], ['8', '10'])).
% 0.71/0.88  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('13', plain, ((v5_orders_2 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('16', plain,
% 0.71/0.88      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.71/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.88      inference('clc', [status(thm)], ['6', '7'])).
% 0.71/0.88  thf(d13_orders_2, axiom,
% 0.71/0.88    (![A:$i]:
% 0.71/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.71/0.88         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.71/0.88       ( ![B:$i]:
% 0.71/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.88           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.71/0.88  thf('17', plain,
% 0.71/0.88      (![X10 : $i, X11 : $i]:
% 0.71/0.88         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.71/0.88          | ((k2_orders_2 @ X11 @ X10) = (a_2_1_orders_2 @ X11 @ X10))
% 0.71/0.88          | ~ (l1_orders_2 @ X11)
% 0.71/0.88          | ~ (v5_orders_2 @ X11)
% 0.71/0.88          | ~ (v4_orders_2 @ X11)
% 0.71/0.88          | ~ (v3_orders_2 @ X11)
% 0.71/0.88          | (v2_struct_0 @ X11))),
% 0.71/0.88      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.71/0.88  thf('18', plain,
% 0.71/0.88      (((v2_struct_0 @ sk_A)
% 0.71/0.88        | ~ (v3_orders_2 @ sk_A)
% 0.71/0.88        | ~ (v4_orders_2 @ sk_A)
% 0.71/0.88        | ~ (v5_orders_2 @ sk_A)
% 0.71/0.88        | ~ (l1_orders_2 @ sk_A)
% 0.71/0.88        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.71/0.88            = (a_2_1_orders_2 @ sk_A @ 
% 0.71/0.88               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.71/0.88      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.88  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('23', plain,
% 0.71/0.88      (((v2_struct_0 @ sk_A)
% 0.71/0.88        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.71/0.88            = (a_2_1_orders_2 @ sk_A @ 
% 0.71/0.88               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.71/0.88      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.71/0.88  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('25', plain,
% 0.71/0.88      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.71/0.88         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.71/0.88      inference('clc', [status(thm)], ['23', '24'])).
% 0.71/0.88  thf('26', plain,
% 0.71/0.88      (![X0 : $i]:
% 0.71/0.88         ((v2_struct_0 @ sk_A)
% 0.71/0.88          | (r2_hidden @ X0 @ 
% 0.71/0.88             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.71/0.88          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.88          | (r2_hidden @ 
% 0.71/0.88             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.71/0.88             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.71/0.88      inference('demod', [status(thm)], ['11', '12', '13', '14', '15', '25'])).
% 0.71/0.88  thf('27', plain,
% 0.71/0.88      (((r2_hidden @ 
% 0.71/0.88         (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.71/0.88         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.71/0.88        | (r2_hidden @ sk_B @ 
% 0.71/0.88           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.71/0.88        | (v2_struct_0 @ sk_A))),
% 0.71/0.88      inference('sup-', [status(thm)], ['0', '26'])).
% 0.71/0.88  thf('28', plain,
% 0.71/0.88      ((~ (r2_hidden @ sk_B @ 
% 0.71/0.88           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.71/0.88        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.71/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.88  thf('29', plain,
% 0.71/0.88      ((~ (r2_hidden @ sk_B @ 
% 0.71/0.88           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.71/0.88         <= (~
% 0.71/0.88             ((r2_hidden @ sk_B @ 
% 0.71/0.88               (k2_orders_2 @ sk_A @ 
% 0.71/0.88                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.88      inference('split', [status(esa)], ['28'])).
% 0.71/0.88  thf('30', plain,
% 0.71/0.88      (~
% 0.71/0.88       ((r2_hidden @ sk_B @ 
% 0.71/0.88         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 0.71/0.89       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.71/0.89      inference('split', [status(esa)], ['28'])).
% 0.71/0.89  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(t24_orders_2, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.71/0.89       ( ![B:$i]:
% 0.71/0.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.89           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.71/0.89  thf('32', plain,
% 0.71/0.89      (![X19 : $i, X20 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.71/0.89          | (r1_orders_2 @ X20 @ X19 @ X19)
% 0.71/0.89          | ~ (l1_orders_2 @ X20)
% 0.71/0.89          | ~ (v3_orders_2 @ X20)
% 0.71/0.89          | (v2_struct_0 @ X20))),
% 0.71/0.89      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.71/0.89  thf('33', plain,
% 0.71/0.89      (((v2_struct_0 @ sk_A)
% 0.71/0.89        | ~ (v3_orders_2 @ sk_A)
% 0.71/0.89        | ~ (l1_orders_2 @ sk_A)
% 0.71/0.89        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.71/0.89      inference('sup-', [status(thm)], ['31', '32'])).
% 0.71/0.89  thf('34', plain, ((v3_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('36', plain,
% 0.71/0.89      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.71/0.89      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.71/0.89  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('38', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.71/0.89      inference('clc', [status(thm)], ['36', '37'])).
% 0.71/0.89  thf(t38_orders_2, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( ( l1_orders_2 @ A ) & ( v3_orders_2 @ A ) ) =>
% 0.71/0.89       ( ![B:$i]:
% 0.71/0.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.89           ( ![C:$i]:
% 0.71/0.89             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.89               ( ( ~( ( ![D:$i]:
% 0.71/0.89                        ( ( ( m1_subset_1 @
% 0.71/0.89                              D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.71/0.89                            ( v6_orders_2 @ D @ A ) ) =>
% 0.71/0.89                          ( ~( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.71/0.89                      ( ( r1_orders_2 @ A @ C @ B ) | 
% 0.71/0.89                        ( r1_orders_2 @ A @ B @ C ) ) ) ) & 
% 0.71/0.89                 ( ~( ( ~( r1_orders_2 @ A @ C @ B ) ) & 
% 0.71/0.89                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.71/0.89                      ( ?[D:$i]:
% 0.71/0.89                        ( ( v6_orders_2 @ D @ A ) & 
% 0.71/0.89                          ( m1_subset_1 @
% 0.71/0.89                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.71/0.89                          ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.71/0.89  thf(zf_stmt_1, axiom,
% 0.71/0.89    (![C:$i,B:$i,A:$i]:
% 0.71/0.89     ( ( ( r1_orders_2 @ A @ B @ C ) | ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.71/0.89       ( zip_tseitin_3 @ C @ B @ A ) ))).
% 0.71/0.89  thf('39', plain,
% 0.71/0.89      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.71/0.89         ((zip_tseitin_3 @ X32 @ X33 @ X34) | ~ (r1_orders_2 @ X34 @ X33 @ X32))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.89  thf('40', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 0.71/0.89      inference('sup-', [status(thm)], ['38', '39'])).
% 0.71/0.89  thf(zf_stmt_2, axiom,
% 0.71/0.89    (![D:$i,C:$i,B:$i,A:$i]:
% 0.71/0.89     ( ( ( zip_tseitin_0 @ D @ A ) => ( ~( zip_tseitin_1 @ D @ C @ B ) ) ) =>
% 0.71/0.89       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.71/0.89  thf('41', plain,
% 0.71/0.89      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.71/0.89         ((zip_tseitin_2 @ X28 @ X29 @ X30 @ X31)
% 0.71/0.89          | (zip_tseitin_1 @ X28 @ X29 @ X30))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.71/0.89  thf('42', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(zf_stmt_3, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.71/0.89  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.71/0.89  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.71/0.89  thf(zf_stmt_6, axiom,
% 0.71/0.89    (![D:$i,C:$i,B:$i]:
% 0.71/0.89     ( ( zip_tseitin_1 @ D @ C @ B ) =>
% 0.71/0.89       ( ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ))).
% 0.71/0.89  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $o).
% 0.71/0.89  thf(zf_stmt_8, axiom,
% 0.71/0.89    (![D:$i,A:$i]:
% 0.71/0.89     ( ( zip_tseitin_0 @ D @ A ) =>
% 0.71/0.89       ( ( v6_orders_2 @ D @ A ) & 
% 0.71/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.71/0.89  thf(zf_stmt_9, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.71/0.89       ( ![B:$i]:
% 0.71/0.89         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.89           ( ![C:$i]:
% 0.71/0.89             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.71/0.89               ( ( ~( ( ?[D:$i]:
% 0.71/0.89                        ( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) & 
% 0.71/0.89                          ( m1_subset_1 @
% 0.71/0.89                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.71/0.89                          ( v6_orders_2 @ D @ A ) ) ) & 
% 0.71/0.89                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.71/0.89                      ( ~( r1_orders_2 @ A @ C @ B ) ) ) ) & 
% 0.71/0.89                 ( ~( ( zip_tseitin_3 @ C @ B @ A ) & 
% 0.71/0.89                      ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.71/0.89  thf('43', plain,
% 0.71/0.89      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 0.71/0.89          | ~ (zip_tseitin_2 @ (sk_D_2 @ X37 @ X35 @ X36) @ X37 @ X35 @ X36)
% 0.71/0.89          | ~ (zip_tseitin_3 @ X37 @ X35 @ X36)
% 0.71/0.89          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.71/0.89          | ~ (l1_orders_2 @ X36)
% 0.71/0.89          | ~ (v3_orders_2 @ X36))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.71/0.89  thf('44', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v3_orders_2 @ sk_A)
% 0.71/0.89          | ~ (l1_orders_2 @ sk_A)
% 0.71/0.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.71/0.89          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.71/0.89      inference('sup-', [status(thm)], ['42', '43'])).
% 0.71/0.89  thf('45', plain, ((v3_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('46', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('47', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.71/0.89          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.71/0.89      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.71/0.89  thf('48', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((zip_tseitin_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B)
% 0.71/0.89          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.71/0.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['41', '47'])).
% 0.71/0.89  thf('49', plain,
% 0.71/0.89      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.71/0.89        | (zip_tseitin_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B))),
% 0.71/0.89      inference('sup-', [status(thm)], ['40', '48'])).
% 0.71/0.89  thf('50', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('51', plain,
% 0.71/0.89      ((zip_tseitin_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B)),
% 0.71/0.89      inference('demod', [status(thm)], ['49', '50'])).
% 0.71/0.89  thf('52', plain,
% 0.71/0.89      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.71/0.89         ((r2_hidden @ X25 @ X26) | ~ (zip_tseitin_1 @ X26 @ X27 @ X25))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.71/0.89  thf('53', plain, ((r2_hidden @ sk_B @ (sk_D_2 @ sk_B @ sk_B @ sk_A))),
% 0.71/0.89      inference('sup-', [status(thm)], ['51', '52'])).
% 0.71/0.89  thf('54', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(redefinition_k6_domain_1, axiom,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.71/0.89       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.71/0.89  thf('55', plain,
% 0.71/0.89      (![X17 : $i, X18 : $i]:
% 0.71/0.89         ((v1_xboole_0 @ X17)
% 0.71/0.89          | ~ (m1_subset_1 @ X18 @ X17)
% 0.71/0.89          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.71/0.89  thf('56', plain,
% 0.71/0.89      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['54', '55'])).
% 0.71/0.89  thf('57', plain,
% 0.71/0.89      (((r2_hidden @ sk_B @ 
% 0.71/0.89         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.71/0.89        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('58', plain,
% 0.71/0.89      (((r2_hidden @ sk_B @ 
% 0.71/0.89         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('split', [status(esa)], ['57'])).
% 0.71/0.89  thf('59', plain,
% 0.71/0.89      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.71/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('clc', [status(thm)], ['6', '7'])).
% 0.71/0.89  thf('60', plain,
% 0.71/0.89      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.71/0.89         (~ (l1_orders_2 @ X12)
% 0.71/0.89          | ~ (v5_orders_2 @ X12)
% 0.71/0.89          | ~ (v4_orders_2 @ X12)
% 0.71/0.89          | ~ (v3_orders_2 @ X12)
% 0.71/0.89          | (v2_struct_0 @ X12)
% 0.71/0.89          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.71/0.89          | ((X15) = (sk_D_1 @ X13 @ X12 @ X15))
% 0.71/0.89          | ~ (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13)))),
% 0.71/0.89      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.71/0.89  thf('61', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X0 @ 
% 0.71/0.89             (a_2_1_orders_2 @ sk_A @ 
% 0.71/0.89              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.71/0.89          | ((X0)
% 0.71/0.89              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ 
% 0.71/0.89                 X0))
% 0.71/0.89          | (v2_struct_0 @ sk_A)
% 0.71/0.89          | ~ (v3_orders_2 @ sk_A)
% 0.71/0.89          | ~ (v4_orders_2 @ sk_A)
% 0.71/0.89          | ~ (v5_orders_2 @ sk_A)
% 0.71/0.89          | ~ (l1_orders_2 @ sk_A))),
% 0.71/0.89      inference('sup-', [status(thm)], ['59', '60'])).
% 0.71/0.89  thf('62', plain,
% 0.71/0.89      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.71/0.89         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.71/0.89      inference('clc', [status(thm)], ['23', '24'])).
% 0.71/0.89  thf('63', plain, ((v3_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('64', plain, ((v4_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('65', plain, ((v5_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('66', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('67', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X0 @ 
% 0.71/0.89             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.71/0.89          | ((X0)
% 0.71/0.89              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ 
% 0.71/0.89                 X0))
% 0.71/0.89          | (v2_struct_0 @ sk_A))),
% 0.71/0.89      inference('demod', [status(thm)], ['61', '62', '63', '64', '65', '66'])).
% 0.71/0.89  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('69', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (((X0)
% 0.71/0.89            = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ X0))
% 0.71/0.89          | ~ (r2_hidden @ X0 @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.71/0.89      inference('clc', [status(thm)], ['67', '68'])).
% 0.71/0.89  thf('70', plain,
% 0.71/0.89      ((((sk_B)
% 0.71/0.89          = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ sk_B)))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['58', '69'])).
% 0.71/0.89  thf('71', plain,
% 0.71/0.89      (((((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))
% 0.71/0.89         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('sup+', [status(thm)], ['56', '70'])).
% 0.71/0.89  thf(t69_enumset1, axiom,
% 0.71/0.89    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.71/0.89  thf('72', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.71/0.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.71/0.89  thf(d2_tarski, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.71/0.89       ( ![D:$i]:
% 0.71/0.89         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.71/0.89  thf('73', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.71/0.89         (((X1) != (X0))
% 0.71/0.89          | (r2_hidden @ X1 @ X2)
% 0.71/0.89          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.71/0.89      inference('cnf', [status(esa)], [d2_tarski])).
% 0.71/0.89  thf('74', plain,
% 0.71/0.89      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.71/0.89      inference('simplify', [status(thm)], ['73'])).
% 0.71/0.89  thf('75', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.71/0.89      inference('sup+', [status(thm)], ['72', '74'])).
% 0.71/0.89  thf('76', plain,
% 0.71/0.89      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['54', '55'])).
% 0.71/0.89  thf('77', plain,
% 0.71/0.89      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.71/0.89         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.71/0.89      inference('clc', [status(thm)], ['23', '24'])).
% 0.71/0.89  thf('78', plain,
% 0.71/0.89      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.71/0.89          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup+', [status(thm)], ['76', '77'])).
% 0.71/0.89  thf('79', plain,
% 0.71/0.89      (((r2_hidden @ sk_B @ 
% 0.71/0.89         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('split', [status(esa)], ['57'])).
% 0.71/0.89  thf('80', plain,
% 0.71/0.89      ((((r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('sup+', [status(thm)], ['78', '79'])).
% 0.71/0.89  thf('81', plain,
% 0.71/0.89      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['54', '55'])).
% 0.71/0.89  thf('82', plain,
% 0.71/0.89      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.71/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('clc', [status(thm)], ['6', '7'])).
% 0.71/0.89  thf('83', plain,
% 0.71/0.89      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.71/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup+', [status(thm)], ['81', '82'])).
% 0.71/0.89  thf('84', plain,
% 0.71/0.89      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.71/0.89         (~ (l1_orders_2 @ X12)
% 0.71/0.89          | ~ (v5_orders_2 @ X12)
% 0.71/0.89          | ~ (v4_orders_2 @ X12)
% 0.71/0.89          | ~ (v3_orders_2 @ X12)
% 0.71/0.89          | (v2_struct_0 @ X12)
% 0.71/0.89          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.71/0.89          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.71/0.89          | (r2_orders_2 @ X12 @ (sk_D_1 @ X13 @ X12 @ X15) @ X14)
% 0.71/0.89          | ~ (r2_hidden @ X14 @ X13)
% 0.71/0.89          | ~ (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13)))),
% 0.71/0.89      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.71/0.89  thf('85', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 0.71/0.89          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 0.71/0.89             X1)
% 0.71/0.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | (v2_struct_0 @ sk_A)
% 0.71/0.89          | ~ (v3_orders_2 @ sk_A)
% 0.71/0.89          | ~ (v4_orders_2 @ sk_A)
% 0.71/0.89          | ~ (v5_orders_2 @ sk_A)
% 0.71/0.89          | ~ (l1_orders_2 @ sk_A))),
% 0.71/0.89      inference('sup-', [status(thm)], ['83', '84'])).
% 0.71/0.89  thf('86', plain, ((v3_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('87', plain, ((v4_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('90', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 0.71/0.89          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 0.71/0.89             X1)
% 0.71/0.89          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | (v2_struct_0 @ sk_A))),
% 0.71/0.89      inference('demod', [status(thm)], ['85', '86', '87', '88', '89'])).
% 0.71/0.89  thf('91', plain,
% 0.71/0.89      ((![X0 : $i]:
% 0.71/0.89          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89           | (v2_struct_0 @ sk_A)
% 0.71/0.89           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89           | (r2_orders_2 @ sk_A @ 
% 0.71/0.89              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 0.71/0.89           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 0.71/0.89           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['80', '90'])).
% 0.71/0.89  thf('92', plain,
% 0.71/0.89      ((![X0 : $i]:
% 0.71/0.89          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 0.71/0.89           | (r2_orders_2 @ sk_A @ 
% 0.71/0.89              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 0.71/0.89           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89           | (v2_struct_0 @ sk_A)
% 0.71/0.89           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('simplify', [status(thm)], ['91'])).
% 0.71/0.89  thf('93', plain,
% 0.71/0.89      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89         | (v2_struct_0 @ sk_A)
% 0.71/0.89         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.71/0.89         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.71/0.89            sk_C)))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['75', '92'])).
% 0.71/0.89  thf('94', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('95', plain,
% 0.71/0.89      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89         | (v2_struct_0 @ sk_A)
% 0.71/0.89         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.71/0.89            sk_C)))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('demod', [status(thm)], ['93', '94'])).
% 0.71/0.89  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('97', plain,
% 0.71/0.89      ((((r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.71/0.89          sk_C)
% 0.71/0.89         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('clc', [status(thm)], ['95', '96'])).
% 0.71/0.89  thf('98', plain,
% 0.71/0.89      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.71/0.89         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('sup+', [status(thm)], ['71', '97'])).
% 0.71/0.89  thf('99', plain,
% 0.71/0.89      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.71/0.89         <= (((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('simplify', [status(thm)], ['98'])).
% 0.71/0.89  thf('100', plain,
% 0.71/0.89      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.71/0.89         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.71/0.89      inference('split', [status(esa)], ['28'])).
% 0.71/0.89  thf('101', plain,
% 0.71/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.71/0.89         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.71/0.89             ((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['99', '100'])).
% 0.71/0.89  thf('102', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 0.71/0.89      inference('sup-', [status(thm)], ['38', '39'])).
% 0.71/0.89  thf('103', plain,
% 0.71/0.89      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.71/0.89         ((zip_tseitin_2 @ X28 @ X29 @ X30 @ X31) | (zip_tseitin_0 @ X28 @ X31))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.71/0.89  thf('104', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.71/0.89          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.71/0.89      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.71/0.89  thf('105', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((zip_tseitin_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.71/0.89          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.71/0.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['103', '104'])).
% 0.71/0.89  thf('106', plain,
% 0.71/0.89      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.71/0.89        | (zip_tseitin_0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_A))),
% 0.71/0.89      inference('sup-', [status(thm)], ['102', '105'])).
% 0.71/0.89  thf('107', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('108', plain, ((zip_tseitin_0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 0.71/0.89      inference('demod', [status(thm)], ['106', '107'])).
% 0.71/0.89  thf('109', plain,
% 0.71/0.89      (![X23 : $i, X24 : $i]:
% 0.71/0.89         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.71/0.89          | ~ (zip_tseitin_0 @ X23 @ X24))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.71/0.89  thf('110', plain,
% 0.71/0.89      ((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ 
% 0.71/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['108', '109'])).
% 0.71/0.89  thf(t5_subset, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.71/0.89          ( v1_xboole_0 @ C ) ) ))).
% 0.71/0.89  thf('111', plain,
% 0.71/0.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X7 @ X8)
% 0.71/0.89          | ~ (v1_xboole_0 @ X9)
% 0.71/0.89          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.71/0.89      inference('cnf', [status(esa)], [t5_subset])).
% 0.71/0.89  thf('112', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['110', '111'])).
% 0.71/0.89  thf('113', plain,
% 0.71/0.89      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))
% 0.71/0.89         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.71/0.89             ((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['101', '112'])).
% 0.71/0.89  thf('114', plain,
% 0.71/0.89      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.71/0.89       ~
% 0.71/0.89       ((r2_hidden @ sk_B @ 
% 0.71/0.89         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['53', '113'])).
% 0.71/0.89  thf('115', plain,
% 0.71/0.89      (~
% 0.71/0.89       ((r2_hidden @ sk_B @ 
% 0.71/0.89         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.71/0.89      inference('sat_resolution*', [status(thm)], ['30', '114'])).
% 0.71/0.89  thf('116', plain,
% 0.71/0.89      (~ (r2_hidden @ sk_B @ 
% 0.71/0.89          (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.71/0.89      inference('simpl_trail', [status(thm)], ['29', '115'])).
% 0.71/0.89  thf('117', plain,
% 0.71/0.89      (((v2_struct_0 @ sk_A)
% 0.71/0.89        | (r2_hidden @ 
% 0.71/0.89           (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.71/0.89           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.71/0.89      inference('clc', [status(thm)], ['27', '116'])).
% 0.71/0.89  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('119', plain,
% 0.71/0.89      ((r2_hidden @ 
% 0.71/0.89        (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.71/0.89        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.71/0.89      inference('clc', [status(thm)], ['117', '118'])).
% 0.71/0.89  thf('120', plain,
% 0.71/0.89      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.71/0.89        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('clc', [status(thm)], ['6', '7'])).
% 0.71/0.89  thf('121', plain,
% 0.71/0.89      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X7 @ X8)
% 0.71/0.89          | ~ (v1_xboole_0 @ X9)
% 0.71/0.89          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.71/0.89      inference('cnf', [status(esa)], [t5_subset])).
% 0.71/0.89  thf('122', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['120', '121'])).
% 0.71/0.89  thf('123', plain,
% 0.71/0.89      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['54', '55'])).
% 0.71/0.89  thf('124', plain,
% 0.71/0.89      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['54', '55'])).
% 0.71/0.89  thf('125', plain,
% 0.71/0.89      ((r2_hidden @ 
% 0.71/0.89        (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 0.71/0.89        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.71/0.89      inference('clc', [status(thm)], ['117', '118'])).
% 0.71/0.89  thf('126', plain,
% 0.71/0.89      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.71/0.89         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup+', [status(thm)], ['124', '125'])).
% 0.71/0.89  thf('127', plain,
% 0.71/0.89      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.71/0.89         (k1_tarski @ sk_C))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup+', [status(thm)], ['123', '126'])).
% 0.71/0.89  thf('128', plain,
% 0.71/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89        | (r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.71/0.89           (k1_tarski @ sk_C)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['127'])).
% 0.71/0.89  thf('129', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.71/0.89      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.71/0.89  thf('130', plain,
% 0.71/0.89      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X4 @ X2)
% 0.71/0.89          | ((X4) = (X3))
% 0.71/0.89          | ((X4) = (X0))
% 0.71/0.89          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.71/0.89      inference('cnf', [status(esa)], [d2_tarski])).
% 0.71/0.89  thf('131', plain,
% 0.71/0.89      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.71/0.89         (((X4) = (X0))
% 0.71/0.89          | ((X4) = (X3))
% 0.71/0.89          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['130'])).
% 0.71/0.89  thf('132', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['129', '131'])).
% 0.71/0.89  thf('133', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['132'])).
% 0.71/0.89  thf('134', plain,
% 0.71/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['128', '133'])).
% 0.71/0.89  thf('135', plain,
% 0.71/0.89      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.71/0.89         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup+', [status(thm)], ['81', '82'])).
% 0.71/0.89  thf('136', plain,
% 0.71/0.89      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.71/0.89         (~ (l1_orders_2 @ X12)
% 0.71/0.89          | ~ (v5_orders_2 @ X12)
% 0.71/0.89          | ~ (v4_orders_2 @ X12)
% 0.71/0.89          | ~ (v3_orders_2 @ X12)
% 0.71/0.89          | (v2_struct_0 @ X12)
% 0.71/0.89          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.71/0.89          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.71/0.89          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.71/0.89          | ((X15) != (X16))
% 0.71/0.89          | ~ (r2_orders_2 @ X12 @ X16 @ (sk_E @ X16 @ X13 @ X12)))),
% 0.71/0.89      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.71/0.89  thf('137', plain,
% 0.71/0.89      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.71/0.89         (~ (r2_orders_2 @ X12 @ X16 @ (sk_E @ X16 @ X13 @ X12))
% 0.71/0.89          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.71/0.89          | (r2_hidden @ X16 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.71/0.89          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.71/0.89          | (v2_struct_0 @ X12)
% 0.71/0.89          | ~ (v3_orders_2 @ X12)
% 0.71/0.89          | ~ (v4_orders_2 @ X12)
% 0.71/0.89          | ~ (v5_orders_2 @ X12)
% 0.71/0.89          | ~ (l1_orders_2 @ X12))),
% 0.71/0.89      inference('simplify', [status(thm)], ['136'])).
% 0.71/0.89  thf('138', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | ~ (l1_orders_2 @ sk_A)
% 0.71/0.89          | ~ (v5_orders_2 @ sk_A)
% 0.71/0.89          | ~ (v4_orders_2 @ sk_A)
% 0.71/0.89          | ~ (v3_orders_2 @ sk_A)
% 0.71/0.89          | (v2_struct_0 @ sk_A)
% 0.71/0.89          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.71/0.89               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['135', '137'])).
% 0.71/0.89  thf('139', plain, ((l1_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('140', plain, ((v5_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('141', plain, ((v4_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('142', plain, ((v3_orders_2 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('143', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | (v2_struct_0 @ sk_A)
% 0.71/0.89          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.71/0.89               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 0.71/0.89      inference('demod', [status(thm)], ['138', '139', '140', '141', '142'])).
% 0.71/0.89  thf('144', plain,
% 0.71/0.89      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.71/0.89        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89        | (v2_struct_0 @ sk_A)
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['134', '143'])).
% 0.71/0.89  thf('145', plain,
% 0.71/0.89      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.71/0.89         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.71/0.89      inference('split', [status(esa)], ['57'])).
% 0.71/0.89  thf('146', plain,
% 0.71/0.89      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.71/0.89       ((r2_hidden @ sk_B @ 
% 0.71/0.89         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.71/0.89      inference('split', [status(esa)], ['57'])).
% 0.71/0.89  thf('147', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.71/0.89      inference('sat_resolution*', [status(thm)], ['30', '114', '146'])).
% 0.71/0.89  thf('148', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.71/0.89      inference('simpl_trail', [status(thm)], ['145', '147'])).
% 0.71/0.89  thf('149', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('150', plain,
% 0.71/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89        | (v2_struct_0 @ sk_A)
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('demod', [status(thm)], ['144', '148', '149'])).
% 0.71/0.89  thf('151', plain,
% 0.71/0.89      (((v2_struct_0 @ sk_A)
% 0.71/0.89        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['150'])).
% 0.71/0.89  thf('152', plain, (~ (v2_struct_0 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('153', plain,
% 0.71/0.89      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.71/0.89        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.71/0.89      inference('clc', [status(thm)], ['151', '152'])).
% 0.71/0.89  thf('154', plain,
% 0.71/0.89      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.71/0.89          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('sup+', [status(thm)], ['76', '77'])).
% 0.71/0.89  thf('155', plain,
% 0.71/0.89      ((~ (r2_hidden @ sk_B @ 
% 0.71/0.89           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.71/0.89         <= (~
% 0.71/0.89             ((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('split', [status(esa)], ['28'])).
% 0.71/0.89  thf('156', plain,
% 0.71/0.89      (((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.71/0.89         <= (~
% 0.71/0.89             ((r2_hidden @ sk_B @ 
% 0.71/0.89               (k2_orders_2 @ sk_A @ 
% 0.71/0.89                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['154', '155'])).
% 0.71/0.89  thf('157', plain,
% 0.71/0.89      (~
% 0.71/0.89       ((r2_hidden @ sk_B @ 
% 0.71/0.89         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.71/0.89      inference('sat_resolution*', [status(thm)], ['30', '114'])).
% 0.71/0.89  thf('158', plain,
% 0.71/0.89      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.71/0.89        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.89      inference('simpl_trail', [status(thm)], ['156', '157'])).
% 0.71/0.89  thf('159', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.71/0.89      inference('clc', [status(thm)], ['153', '158'])).
% 0.71/0.89  thf('160', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 0.71/0.89      inference('demod', [status(thm)], ['122', '159'])).
% 0.71/0.89  thf('161', plain, ($false), inference('sup-', [status(thm)], ['119', '160'])).
% 0.71/0.89  
% 0.71/0.89  % SZS output end Refutation
% 0.71/0.89  
% 0.71/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
