%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r0Uh4bn2pk

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:55 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 180 expanded)
%              Number of leaves         :   41 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  823 (2196 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t50_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ~ ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_orders_2])).

thf('0',plain,(
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

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r1_orders_2 @ X16 @ X15 @ X15 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_3 @ X28 @ X29 @ X30 )
      | ~ ( r1_orders_2 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    zip_tseitin_3 @ sk_B @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ D @ A )
       => ~ ( zip_tseitin_1 @ D @ C @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_2 @ X24 @ X25 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_1 @ X33 @ X31 @ X32 ) @ X33 @ X31 @ X32 )
      | ~ ( zip_tseitin_3 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ ( sk_D_1 @ sk_B @ sk_B @ sk_A ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    zip_tseitin_1 @ ( sk_D_1 @ sk_B @ sk_B @ sk_A ) @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X22 @ X23 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    zip_tseitin_3 @ sk_B @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_2 @ X24 @ X25 @ X26 @ X27 )
      | ( zip_tseitin_0 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_1 @ sk_B @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    zip_tseitin_0 @ ( sk_D_1 @ sk_B @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( zip_tseitin_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('31',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('36',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X18 ) @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(t49_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( r2_hidden @ B @ C )
                  & ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( r2_hidden @ X35 @ ( k2_orders_2 @ X36 @ X37 ) )
      | ~ ( r2_hidden @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v5_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t49_orders_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ~ ( r2_hidden @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','57'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('59',plain,(
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

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('61',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','61'])).

thf('63',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_D_1 @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','63'])).

thf('65',plain,(
    $false ),
    inference('sup-',[status(thm)],['22','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r0Uh4bn2pk
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:36:53 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 98 iterations in 0.071s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.36/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.54  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.54  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.36/0.54  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.36/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.54  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.36/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.36/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.36/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.36/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(t50_orders_2, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.36/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54           ( ~( r2_hidden @
% 0.36/0.54                B @ 
% 0.36/0.54                ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.36/0.54            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54              ( ~( r2_hidden @
% 0.36/0.54                   B @ 
% 0.36/0.54                   ( k2_orders_2 @
% 0.36/0.54                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t50_orders_2])).
% 0.36/0.54  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t24_orders_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X15 : $i, X16 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.36/0.54          | (r1_orders_2 @ X16 @ X15 @ X15)
% 0.36/0.54          | ~ (l1_orders_2 @ X16)
% 0.36/0.54          | ~ (v3_orders_2 @ X16)
% 0.36/0.54          | (v2_struct_0 @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | ~ (v3_orders_2 @ sk_A)
% 0.36/0.54        | ~ (l1_orders_2 @ sk_A)
% 0.36/0.54        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.36/0.54  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('7', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.36/0.54      inference('clc', [status(thm)], ['5', '6'])).
% 0.36/0.54  thf(t38_orders_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( l1_orders_2 @ A ) & ( v3_orders_2 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54               ( ( ~( ( ![D:$i]:
% 0.36/0.54                        ( ( ( m1_subset_1 @
% 0.36/0.54                              D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.36/0.54                            ( v6_orders_2 @ D @ A ) ) =>
% 0.36/0.54                          ( ~( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.36/0.54                      ( ( r1_orders_2 @ A @ C @ B ) | 
% 0.36/0.54                        ( r1_orders_2 @ A @ B @ C ) ) ) ) & 
% 0.36/0.54                 ( ~( ( ~( r1_orders_2 @ A @ C @ B ) ) & 
% 0.36/0.54                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.36/0.54                      ( ?[D:$i]:
% 0.36/0.54                        ( ( v6_orders_2 @ D @ A ) & 
% 0.36/0.54                          ( m1_subset_1 @
% 0.36/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.36/0.54                          ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_1, axiom,
% 0.36/0.54    (![C:$i,B:$i,A:$i]:
% 0.36/0.54     ( ( ( r1_orders_2 @ A @ B @ C ) | ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.36/0.54       ( zip_tseitin_3 @ C @ B @ A ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.54         ((zip_tseitin_3 @ X28 @ X29 @ X30) | ~ (r1_orders_2 @ X30 @ X29 @ X28))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.54  thf('9', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf(zf_stmt_2, axiom,
% 0.36/0.54    (![D:$i,C:$i,B:$i,A:$i]:
% 0.36/0.54     ( ( ( zip_tseitin_0 @ D @ A ) => ( ~( zip_tseitin_1 @ D @ C @ B ) ) ) =>
% 0.36/0.54       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.54         ((zip_tseitin_2 @ X24 @ X25 @ X26 @ X27)
% 0.36/0.54          | (zip_tseitin_1 @ X24 @ X25 @ X26))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.54  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(zf_stmt_3, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_6, axiom,
% 0.36/0.54    (![D:$i,C:$i,B:$i]:
% 0.36/0.54     ( ( zip_tseitin_1 @ D @ C @ B ) =>
% 0.36/0.54       ( ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ))).
% 0.36/0.54  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_8, axiom,
% 0.36/0.54    (![D:$i,A:$i]:
% 0.36/0.54     ( ( zip_tseitin_0 @ D @ A ) =>
% 0.36/0.54       ( ( v6_orders_2 @ D @ A ) & 
% 0.36/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_9, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54               ( ( ~( ( ?[D:$i]:
% 0.36/0.54                        ( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) & 
% 0.36/0.54                          ( m1_subset_1 @
% 0.36/0.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.36/0.54                          ( v6_orders_2 @ D @ A ) ) ) & 
% 0.36/0.54                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.36/0.54                      ( ~( r1_orders_2 @ A @ C @ B ) ) ) ) & 
% 0.36/0.54                 ( ~( ( zip_tseitin_3 @ C @ B @ A ) & 
% 0.36/0.54                      ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.36/0.54          | ~ (zip_tseitin_2 @ (sk_D_1 @ X33 @ X31 @ X32) @ X33 @ X31 @ X32)
% 0.36/0.54          | ~ (zip_tseitin_3 @ X33 @ X31 @ X32)
% 0.36/0.54          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.36/0.54          | ~ (l1_orders_2 @ X32)
% 0.36/0.54          | ~ (v3_orders_2 @ X32))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v3_orders_2 @ sk_A)
% 0.36/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.54          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.36/0.54          | ~ (zip_tseitin_2 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.54  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.54          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.36/0.54          | ~ (zip_tseitin_2 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B)
% 0.36/0.54          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['10', '16'])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.54        | (zip_tseitin_1 @ (sk_D_1 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['9', '17'])).
% 0.36/0.54  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      ((zip_tseitin_1 @ (sk_D_1 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B)),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.54         ((r2_hidden @ X21 @ X22) | ~ (zip_tseitin_1 @ X22 @ X23 @ X21))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.36/0.54  thf('22', plain, ((r2_hidden @ sk_B @ (sk_D_1 @ sk_B @ sk_B @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.54  thf('23', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.54         ((zip_tseitin_2 @ X24 @ X25 @ X26 @ X27) | (zip_tseitin_0 @ X24 @ X27))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.36/0.54          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.36/0.54          | ~ (zip_tseitin_2 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.36/0.54          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.54        | (zip_tseitin_0 @ (sk_D_1 @ sk_B @ sk_B @ sk_A) @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['23', '26'])).
% 0.36/0.54  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('29', plain, ((zip_tseitin_0 @ (sk_D_1 @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 0.36/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X19 : $i, X20 : $i]:
% 0.36/0.54         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.36/0.54          | ~ (zip_tseitin_0 @ X19 @ X20))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      ((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_B @ sk_A) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.54  thf(t5_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.36/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X10 @ X11)
% 0.36/0.54          | ~ (v1_xboole_0 @ X12)
% 0.36/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ (sk_D_1 @ sk_B @ sk_B @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.54  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i]:
% 0.36/0.54         ((v1_xboole_0 @ X13)
% 0.36/0.54          | ~ (m1_subset_1 @ X14 @ X13)
% 0.36/0.54          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      ((r2_hidden @ sk_B @ 
% 0.36/0.54        (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('38', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t35_orders_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.36/0.54             ( m1_subset_1 @
% 0.36/0.54               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.36/0.54               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X17 : $i, X18 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.36/0.54          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X18) @ X17) @ 
% 0.36/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.36/0.54          | ~ (l1_orders_2 @ X18)
% 0.36/0.54          | ~ (v3_orders_2 @ X18)
% 0.36/0.54          | (v2_struct_0 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | ~ (v3_orders_2 @ sk_A)
% 0.36/0.54        | ~ (l1_orders_2 @ sk_A)
% 0.36/0.54        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.54  thf('41', plain, ((v3_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (((v2_struct_0 @ sk_A)
% 0.36/0.54        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.36/0.54           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.54      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.36/0.54  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.36/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('clc', [status(thm)], ['43', '44'])).
% 0.36/0.54  thf(t49_orders_2, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.36/0.54         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.54               ( ~( ( r2_hidden @ B @ C ) & 
% 0.36/0.54                    ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 0.36/0.54          | ~ (r2_hidden @ X35 @ (k2_orders_2 @ X36 @ X37))
% 0.36/0.54          | ~ (r2_hidden @ X35 @ X37)
% 0.36/0.54          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.36/0.54          | ~ (l1_orders_2 @ X36)
% 0.36/0.54          | ~ (v5_orders_2 @ X36)
% 0.36/0.54          | ~ (v4_orders_2 @ X36)
% 0.36/0.54          | ~ (v3_orders_2 @ X36)
% 0.36/0.54          | (v2_struct_0 @ X36))),
% 0.36/0.54      inference('cnf', [status(esa)], [t49_orders_2])).
% 0.36/0.54  thf('47', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | ~ (v3_orders_2 @ sk_A)
% 0.36/0.54          | ~ (v4_orders_2 @ sk_A)
% 0.36/0.54          | ~ (v5_orders_2 @ sk_A)
% 0.36/0.54          | ~ (l1_orders_2 @ sk_A)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ 
% 0.36/0.54               (k2_orders_2 @ sk_A @ 
% 0.36/0.54                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.36/0.54  thf('48', plain, ((v3_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('49', plain, ((v4_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('50', plain, ((v5_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((v2_struct_0 @ sk_A)
% 0.36/0.54          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ 
% 0.36/0.54               (k2_orders_2 @ sk_A @ 
% 0.36/0.54                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.36/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.54        | ~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.54        | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['37', '52'])).
% 0.36/0.54  thf('54', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('55', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.54        | (v2_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['53', '54'])).
% 0.36/0.54  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('57', plain,
% 0.36/0.54      (~ (r2_hidden @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.36/0.54      inference('clc', [status(thm)], ['55', '56'])).
% 0.36/0.54  thf('58', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.36/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['36', '57'])).
% 0.36/0.54  thf(t69_enumset1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.54  thf('59', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf(d2_tarski, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.36/0.54       ( ![D:$i]:
% 0.36/0.54         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.36/0.54  thf('60', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.54         (((X1) != (X0))
% 0.36/0.54          | (r2_hidden @ X1 @ X2)
% 0.36/0.54          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.36/0.54  thf('61', plain,
% 0.36/0.54      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['60'])).
% 0.36/0.54  thf('62', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['59', '61'])).
% 0.36/0.54  thf('63', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['58', '62'])).
% 0.36/0.54  thf('64', plain,
% 0.36/0.54      (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_1 @ sk_B @ sk_B @ sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['33', '63'])).
% 0.36/0.54  thf('65', plain, ($false), inference('sup-', [status(thm)], ['22', '64'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
