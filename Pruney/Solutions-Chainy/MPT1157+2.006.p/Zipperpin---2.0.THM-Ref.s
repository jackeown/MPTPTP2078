%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ayxwS0ycPx

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:57 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  201 (1237 expanded)
%              Number of leaves         :   47 ( 372 expanded)
%              Depth                    :   32
%              Number of atoms          : 2014 (22428 expanded)
%              Number of equality atoms :   42 ( 150 expanded)
%              Maximal formula depth    :   20 (   7 average)

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

thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

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

thf(t51_orders_2,conjecture,(
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
              <=> ( r2_hidden @ C @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )).

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
                <=> ( r2_hidden @ C @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_orders_2])).

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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( r1_orders_2 @ X20 @ X19 @ X19 )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_3 @ X32 @ X33 @ X34 )
      | ~ ( r1_orders_2 @ X34 @ X33 @ X32 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_2 @ X28 @ X29 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X28 @ X29 @ X30 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X37 @ X35 @ X36 ) @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_3 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
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
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    zip_tseitin_1 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X26 @ X27 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    zip_tseitin_3 @ sk_B @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_2 @ X28 @ X29 @ X30 @ X31 )
      | ( zip_tseitin_0 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    zip_tseitin_0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( zip_tseitin_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('31',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('37',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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

thf('46',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf(fraenkel_a_2_0_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v3_orders_2 @ B )
        & ( v4_orders_2 @ B )
        & ( v5_orders_2 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) )
      <=> ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
               => ( ( r2_hidden @ E @ C )
                 => ( r2_orders_2 @ B @ E @ D ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ X15 @ ( a_2_0_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( X15 != X16 )
      | ( r2_hidden @ ( sk_E @ X16 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('48',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_E @ X16 @ X13 @ X12 ) @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X16 @ ( a_2_0_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,
    ( ( r2_hidden @ ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','54'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('56',plain,(
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

thf('57',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('58',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('63',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(d12_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_orders_2 @ A @ B )
            = ( a_2_0_orders_2 @ A @ B ) ) ) ) )).

thf('64',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k1_orders_2 @ X11 @ X10 )
        = ( a_2_0_orders_2 @ X11 @ X10 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d12_orders_2])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['74'])).

thf('78',plain,(
    r2_hidden @ sk_B @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('79',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('80',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['80'])).

thf('82',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('83',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( X15
        = ( sk_D_1 @ X13 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( a_2_0_orders_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['70','71'])).

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
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_C
      = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','92'])).

thf('94',plain,
    ( ( ( sk_C
        = ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','93'])).

thf('95',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('97',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','97'])).

thf('99',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','72'])).

thf('100',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['80'])).

thf('101',plain,
    ( ( ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf('103',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r2_orders_2 @ X12 @ X14 @ ( sk_D_1 @ X13 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( a_2_0_orders_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['101','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['94','116'])).

thf('118',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['74'])).

thf('120',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('122',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','122'])).

thf('124',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['77','123'])).

thf('125',plain,
    ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['76','124'])).

thf('126',plain,
    ( ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','125'])).

thf('127',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf('131',plain,(
    ! [X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ X15 @ ( a_2_0_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( X15 != X16 )
      | ~ ( r2_orders_2 @ X12 @ ( sk_E @ X16 @ X13 @ X12 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('132',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ~ ( r2_orders_2 @ X12 @ ( sk_E @ X16 @ X13 @ X12 ) @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X16 @ ( a_2_0_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','132'])).

thf('134',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134','135','136','137'])).

thf('139',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','138'])).

thf('140',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['80'])).

thf('141',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['80'])).

thf('142',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['77','123','141'])).

thf('143',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['140','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['139','143','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['76','124'])).

thf('150',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','150'])).

thf('152',plain,(
    $false ),
    inference('sup-',[status(thm)],['22','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ayxwS0ycPx
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:42:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.66/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.83  % Solved by: fo/fo7.sh
% 0.66/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.83  % done 651 iterations in 0.368s
% 0.66/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.83  % SZS output start Refutation
% 0.66/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.83  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.66/0.83  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.66/0.83  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.66/0.83  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.66/0.83  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.66/0.83  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.66/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.66/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.66/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.66/0.83  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 0.66/0.83  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.66/0.83  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.66/0.83  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.66/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.66/0.83  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.66/0.83  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.66/0.83  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.66/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.66/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.83  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.66/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.66/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.83  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.66/0.83  thf(t51_orders_2, conjecture,
% 0.66/0.83    (![A:$i]:
% 0.66/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.66/0.83         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.66/0.83       ( ![B:$i]:
% 0.66/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.66/0.83           ( ![C:$i]:
% 0.66/0.83             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.66/0.83               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.66/0.83                 ( r2_hidden @
% 0.66/0.83                   C @ 
% 0.66/0.83                   ( k1_orders_2 @
% 0.66/0.83                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ))).
% 0.66/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.83    (~( ![A:$i]:
% 0.66/0.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.66/0.83            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.66/0.83          ( ![B:$i]:
% 0.66/0.83            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.66/0.83              ( ![C:$i]:
% 0.66/0.83                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.66/0.83                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.66/0.83                    ( r2_hidden @
% 0.66/0.83                      C @ 
% 0.66/0.83                      ( k1_orders_2 @
% 0.66/0.83                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ) )),
% 0.66/0.83    inference('cnf.neg', [status(esa)], [t51_orders_2])).
% 0.66/0.83  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf(t24_orders_2, axiom,
% 0.66/0.83    (![A:$i]:
% 0.66/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.66/0.83       ( ![B:$i]:
% 0.66/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.66/0.83           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.66/0.83  thf('1', plain,
% 0.66/0.83      (![X19 : $i, X20 : $i]:
% 0.66/0.83         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.66/0.83          | (r1_orders_2 @ X20 @ X19 @ X19)
% 0.66/0.83          | ~ (l1_orders_2 @ X20)
% 0.66/0.83          | ~ (v3_orders_2 @ X20)
% 0.66/0.83          | (v2_struct_0 @ X20))),
% 0.66/0.83      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.66/0.83  thf('2', plain,
% 0.66/0.83      (((v2_struct_0 @ sk_A)
% 0.66/0.83        | ~ (v3_orders_2 @ sk_A)
% 0.66/0.83        | ~ (l1_orders_2 @ sk_A)
% 0.66/0.83        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.66/0.83      inference('sup-', [status(thm)], ['0', '1'])).
% 0.66/0.83  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('5', plain,
% 0.66/0.83      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.66/0.83      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.66/0.83  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('7', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.66/0.83      inference('clc', [status(thm)], ['5', '6'])).
% 0.66/0.83  thf(t38_orders_2, axiom,
% 0.66/0.83    (![A:$i]:
% 0.66/0.83     ( ( ( l1_orders_2 @ A ) & ( v3_orders_2 @ A ) ) =>
% 0.66/0.83       ( ![B:$i]:
% 0.66/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.66/0.83           ( ![C:$i]:
% 0.66/0.83             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.66/0.83               ( ( ~( ( ![D:$i]:
% 0.66/0.83                        ( ( ( m1_subset_1 @
% 0.66/0.83                              D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.66/0.83                            ( v6_orders_2 @ D @ A ) ) =>
% 0.66/0.83                          ( ~( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.66/0.83                      ( ( r1_orders_2 @ A @ C @ B ) | 
% 0.66/0.83                        ( r1_orders_2 @ A @ B @ C ) ) ) ) & 
% 0.66/0.83                 ( ~( ( ~( r1_orders_2 @ A @ C @ B ) ) & 
% 0.66/0.83                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.66/0.83                      ( ?[D:$i]:
% 0.66/0.83                        ( ( v6_orders_2 @ D @ A ) & 
% 0.66/0.83                          ( m1_subset_1 @
% 0.66/0.83                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.66/0.83                          ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.83  thf(zf_stmt_1, axiom,
% 0.66/0.83    (![C:$i,B:$i,A:$i]:
% 0.66/0.83     ( ( ( r1_orders_2 @ A @ B @ C ) | ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.66/0.83       ( zip_tseitin_3 @ C @ B @ A ) ))).
% 0.66/0.83  thf('8', plain,
% 0.66/0.83      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.66/0.83         ((zip_tseitin_3 @ X32 @ X33 @ X34) | ~ (r1_orders_2 @ X34 @ X33 @ X32))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.66/0.83  thf('9', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 0.66/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.66/0.83  thf(zf_stmt_2, axiom,
% 0.66/0.83    (![D:$i,C:$i,B:$i,A:$i]:
% 0.66/0.83     ( ( ( zip_tseitin_0 @ D @ A ) => ( ~( zip_tseitin_1 @ D @ C @ B ) ) ) =>
% 0.66/0.83       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.66/0.83  thf('10', plain,
% 0.66/0.83      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.66/0.83         ((zip_tseitin_2 @ X28 @ X29 @ X30 @ X31)
% 0.66/0.83          | (zip_tseitin_1 @ X28 @ X29 @ X30))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.83  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf(zf_stmt_3, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.66/0.83  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.66/0.83  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.66/0.83  thf(zf_stmt_6, axiom,
% 0.66/0.83    (![D:$i,C:$i,B:$i]:
% 0.66/0.83     ( ( zip_tseitin_1 @ D @ C @ B ) =>
% 0.66/0.83       ( ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ))).
% 0.66/0.83  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $o).
% 0.66/0.83  thf(zf_stmt_8, axiom,
% 0.66/0.83    (![D:$i,A:$i]:
% 0.66/0.83     ( ( zip_tseitin_0 @ D @ A ) =>
% 0.66/0.83       ( ( v6_orders_2 @ D @ A ) & 
% 0.66/0.83         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.66/0.83  thf(zf_stmt_9, axiom,
% 0.66/0.83    (![A:$i]:
% 0.66/0.83     ( ( ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.66/0.83       ( ![B:$i]:
% 0.66/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.66/0.83           ( ![C:$i]:
% 0.66/0.83             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.66/0.83               ( ( ~( ( ?[D:$i]:
% 0.66/0.83                        ( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) & 
% 0.66/0.83                          ( m1_subset_1 @
% 0.66/0.83                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.66/0.83                          ( v6_orders_2 @ D @ A ) ) ) & 
% 0.66/0.83                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.66/0.83                      ( ~( r1_orders_2 @ A @ C @ B ) ) ) ) & 
% 0.66/0.83                 ( ~( ( zip_tseitin_3 @ C @ B @ A ) & 
% 0.66/0.83                      ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.83  thf('12', plain,
% 0.66/0.83      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.66/0.83         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 0.66/0.83          | ~ (zip_tseitin_2 @ (sk_D_2 @ X37 @ X35 @ X36) @ X37 @ X35 @ X36)
% 0.66/0.83          | ~ (zip_tseitin_3 @ X37 @ X35 @ X36)
% 0.66/0.83          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.66/0.83          | ~ (l1_orders_2 @ X36)
% 0.66/0.83          | ~ (v3_orders_2 @ X36))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.66/0.83  thf('13', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         (~ (v3_orders_2 @ sk_A)
% 0.66/0.83          | ~ (l1_orders_2 @ sk_A)
% 0.66/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.66/0.83          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.66/0.83          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.66/0.83      inference('sup-', [status(thm)], ['11', '12'])).
% 0.66/0.83  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('16', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.66/0.83          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.66/0.83          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.66/0.83      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.66/0.83  thf('17', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         ((zip_tseitin_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B)
% 0.66/0.83          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.66/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['10', '16'])).
% 0.66/0.83  thf('18', plain,
% 0.66/0.83      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.66/0.83        | (zip_tseitin_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B))),
% 0.66/0.83      inference('sup-', [status(thm)], ['9', '17'])).
% 0.66/0.83  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('20', plain,
% 0.66/0.83      ((zip_tseitin_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B)),
% 0.66/0.83      inference('demod', [status(thm)], ['18', '19'])).
% 0.66/0.83  thf('21', plain,
% 0.66/0.83      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.66/0.83         ((r2_hidden @ X25 @ X26) | ~ (zip_tseitin_1 @ X26 @ X27 @ X25))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.66/0.83  thf('22', plain, ((r2_hidden @ sk_B @ (sk_D_2 @ sk_B @ sk_B @ sk_A))),
% 0.66/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.66/0.83  thf('23', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 0.66/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.66/0.83  thf('24', plain,
% 0.66/0.83      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.66/0.83         ((zip_tseitin_2 @ X28 @ X29 @ X30 @ X31) | (zip_tseitin_0 @ X28 @ X31))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.83  thf('25', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.66/0.83          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.66/0.83          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.66/0.83      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.66/0.83  thf('26', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         ((zip_tseitin_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.66/0.83          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.66/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['24', '25'])).
% 0.66/0.83  thf('27', plain,
% 0.66/0.83      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.66/0.83        | (zip_tseitin_0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_A))),
% 0.66/0.83      inference('sup-', [status(thm)], ['23', '26'])).
% 0.66/0.83  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('29', plain, ((zip_tseitin_0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 0.66/0.83      inference('demod', [status(thm)], ['27', '28'])).
% 0.66/0.83  thf('30', plain,
% 0.66/0.83      (![X23 : $i, X24 : $i]:
% 0.66/0.83         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.66/0.83          | ~ (zip_tseitin_0 @ X23 @ X24))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.66/0.83  thf('31', plain,
% 0.66/0.83      ((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ 
% 0.66/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['29', '30'])).
% 0.66/0.83  thf(t5_subset, axiom,
% 0.66/0.83    (![A:$i,B:$i,C:$i]:
% 0.66/0.83     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.66/0.83          ( v1_xboole_0 @ C ) ) ))).
% 0.66/0.83  thf('32', plain,
% 0.66/0.83      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.66/0.83         (~ (r2_hidden @ X7 @ X8)
% 0.66/0.83          | ~ (v1_xboole_0 @ X9)
% 0.66/0.83          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.66/0.83      inference('cnf', [status(esa)], [t5_subset])).
% 0.66/0.83  thf('33', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.83          | ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['31', '32'])).
% 0.66/0.83  thf('34', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf(redefinition_k6_domain_1, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.66/0.83       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.66/0.83  thf('36', plain,
% 0.66/0.83      (![X17 : $i, X18 : $i]:
% 0.66/0.83         ((v1_xboole_0 @ X17)
% 0.66/0.83          | ~ (m1_subset_1 @ X18 @ X17)
% 0.66/0.83          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.66/0.83      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.66/0.83  thf('37', plain,
% 0.66/0.83      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.66/0.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['35', '36'])).
% 0.66/0.83  thf('38', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf(t35_orders_2, axiom,
% 0.66/0.83    (![A:$i]:
% 0.66/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.66/0.83       ( ![B:$i]:
% 0.66/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.66/0.83           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.66/0.83             ( m1_subset_1 @
% 0.66/0.83               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.66/0.84               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.66/0.84  thf('39', plain,
% 0.66/0.84      (![X21 : $i, X22 : $i]:
% 0.66/0.84         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.66/0.84          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21) @ 
% 0.66/0.84             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.66/0.84          | ~ (l1_orders_2 @ X22)
% 0.66/0.84          | ~ (v3_orders_2 @ X22)
% 0.66/0.84          | (v2_struct_0 @ X22))),
% 0.66/0.84      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.66/0.84  thf('40', plain,
% 0.66/0.84      (((v2_struct_0 @ sk_A)
% 0.66/0.84        | ~ (v3_orders_2 @ sk_A)
% 0.66/0.84        | ~ (l1_orders_2 @ sk_A)
% 0.66/0.84        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.66/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['38', '39'])).
% 0.66/0.84  thf('41', plain, ((v3_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('43', plain,
% 0.66/0.84      (((v2_struct_0 @ sk_A)
% 0.66/0.84        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.66/0.84           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.66/0.84      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.66/0.84  thf('44', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('45', plain,
% 0.66/0.84      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.66/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('clc', [status(thm)], ['43', '44'])).
% 0.66/0.84  thf('46', plain,
% 0.66/0.84      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.66/0.84         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['37', '45'])).
% 0.66/0.84  thf(fraenkel_a_2_0_orders_2, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.66/0.84         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.66/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.66/0.84       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 0.66/0.84         ( ?[D:$i]:
% 0.66/0.84           ( ( ![E:$i]:
% 0.66/0.84               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.66/0.84                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 0.66/0.84             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.66/0.84  thf('47', plain,
% 0.66/0.84      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.66/0.84         (~ (l1_orders_2 @ X12)
% 0.66/0.84          | ~ (v5_orders_2 @ X12)
% 0.66/0.84          | ~ (v4_orders_2 @ X12)
% 0.66/0.84          | ~ (v3_orders_2 @ X12)
% 0.66/0.84          | (v2_struct_0 @ X12)
% 0.66/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.66/0.84          | (r2_hidden @ X15 @ (a_2_0_orders_2 @ X12 @ X13))
% 0.66/0.84          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.66/0.84          | ((X15) != (X16))
% 0.66/0.84          | (r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13))),
% 0.66/0.84      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.66/0.84  thf('48', plain,
% 0.66/0.84      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.66/0.84         ((r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13)
% 0.66/0.84          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.66/0.84          | (r2_hidden @ X16 @ (a_2_0_orders_2 @ X12 @ X13))
% 0.66/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.66/0.84          | (v2_struct_0 @ X12)
% 0.66/0.84          | ~ (v3_orders_2 @ X12)
% 0.66/0.84          | ~ (v4_orders_2 @ X12)
% 0.66/0.84          | ~ (v5_orders_2 @ X12)
% 0.66/0.84          | ~ (l1_orders_2 @ X12))),
% 0.66/0.84      inference('simplify', [status(thm)], ['47'])).
% 0.66/0.84  thf('49', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | ~ (l1_orders_2 @ sk_A)
% 0.66/0.84          | ~ (v5_orders_2 @ sk_A)
% 0.66/0.84          | ~ (v4_orders_2 @ sk_A)
% 0.66/0.84          | ~ (v3_orders_2 @ sk_A)
% 0.66/0.84          | (v2_struct_0 @ sk_A)
% 0.66/0.84          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.66/0.84             (k1_tarski @ sk_B)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['46', '48'])).
% 0.66/0.84  thf('50', plain, ((l1_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('51', plain, ((v5_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('52', plain, ((v4_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('53', plain, ((v3_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('54', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | (v2_struct_0 @ sk_A)
% 0.66/0.84          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.66/0.84             (k1_tarski @ sk_B)))),
% 0.66/0.84      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.66/0.84  thf('55', plain,
% 0.66/0.84      (((r2_hidden @ (sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.66/0.84         (k1_tarski @ sk_B))
% 0.66/0.84        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84        | (v2_struct_0 @ sk_A)
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['34', '54'])).
% 0.66/0.84  thf(t69_enumset1, axiom,
% 0.66/0.84    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.66/0.84  thf('56', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.66/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.66/0.84  thf(d2_tarski, axiom,
% 0.66/0.84    (![A:$i,B:$i,C:$i]:
% 0.66/0.84     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.66/0.84       ( ![D:$i]:
% 0.66/0.84         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.66/0.84  thf('57', plain,
% 0.66/0.84      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X4 @ X2)
% 0.66/0.84          | ((X4) = (X3))
% 0.66/0.84          | ((X4) = (X0))
% 0.66/0.84          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.66/0.84      inference('cnf', [status(esa)], [d2_tarski])).
% 0.66/0.84  thf('58', plain,
% 0.66/0.84      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.66/0.84         (((X4) = (X0))
% 0.66/0.84          | ((X4) = (X3))
% 0.66/0.84          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.66/0.84      inference('simplify', [status(thm)], ['57'])).
% 0.66/0.84  thf('59', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['56', '58'])).
% 0.66/0.84  thf('60', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.66/0.84      inference('simplify', [status(thm)], ['59'])).
% 0.66/0.84  thf('61', plain,
% 0.66/0.84      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84        | (v2_struct_0 @ sk_A)
% 0.66/0.84        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84        | ((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['55', '60'])).
% 0.66/0.84  thf('62', plain,
% 0.66/0.84      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['35', '36'])).
% 0.66/0.84  thf('63', plain,
% 0.66/0.84      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.66/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('clc', [status(thm)], ['43', '44'])).
% 0.66/0.84  thf(d12_orders_2, axiom,
% 0.66/0.84    (![A:$i]:
% 0.66/0.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.66/0.84         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.66/0.84       ( ![B:$i]:
% 0.66/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.66/0.84           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 0.66/0.84  thf('64', plain,
% 0.66/0.84      (![X10 : $i, X11 : $i]:
% 0.66/0.84         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.66/0.84          | ((k1_orders_2 @ X11 @ X10) = (a_2_0_orders_2 @ X11 @ X10))
% 0.66/0.84          | ~ (l1_orders_2 @ X11)
% 0.66/0.84          | ~ (v5_orders_2 @ X11)
% 0.66/0.84          | ~ (v4_orders_2 @ X11)
% 0.66/0.84          | ~ (v3_orders_2 @ X11)
% 0.66/0.84          | (v2_struct_0 @ X11))),
% 0.66/0.84      inference('cnf', [status(esa)], [d12_orders_2])).
% 0.66/0.84  thf('65', plain,
% 0.66/0.84      (((v2_struct_0 @ sk_A)
% 0.66/0.84        | ~ (v3_orders_2 @ sk_A)
% 0.66/0.84        | ~ (v4_orders_2 @ sk_A)
% 0.66/0.84        | ~ (v5_orders_2 @ sk_A)
% 0.66/0.84        | ~ (l1_orders_2 @ sk_A)
% 0.66/0.84        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.84            = (a_2_0_orders_2 @ sk_A @ 
% 0.66/0.84               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['63', '64'])).
% 0.66/0.84  thf('66', plain, ((v3_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('67', plain, ((v4_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('68', plain, ((v5_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('70', plain,
% 0.66/0.84      (((v2_struct_0 @ sk_A)
% 0.66/0.84        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.84            = (a_2_0_orders_2 @ sk_A @ 
% 0.66/0.84               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.66/0.84      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.66/0.84  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('72', plain,
% 0.66/0.84      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.84         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.66/0.84      inference('clc', [status(thm)], ['70', '71'])).
% 0.66/0.84  thf('73', plain,
% 0.66/0.84      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.84          = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['62', '72'])).
% 0.66/0.84  thf('74', plain,
% 0.66/0.84      ((~ (r2_hidden @ sk_C @ 
% 0.66/0.84           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.66/0.84        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('75', plain,
% 0.66/0.84      ((~ (r2_hidden @ sk_C @ 
% 0.66/0.84           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.66/0.84         <= (~
% 0.66/0.84             ((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('split', [status(esa)], ['74'])).
% 0.66/0.84  thf('76', plain,
% 0.66/0.84      (((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.66/0.84         <= (~
% 0.66/0.84             ((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['73', '75'])).
% 0.66/0.84  thf('77', plain,
% 0.66/0.84      (~
% 0.66/0.84       ((r2_hidden @ sk_C @ 
% 0.66/0.84         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))) | 
% 0.66/0.84       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.66/0.84      inference('split', [status(esa)], ['74'])).
% 0.66/0.84  thf('78', plain, ((r2_hidden @ sk_B @ (sk_D_2 @ sk_B @ sk_B @ sk_A))),
% 0.66/0.84      inference('sup-', [status(thm)], ['20', '21'])).
% 0.66/0.84  thf('79', plain,
% 0.66/0.84      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['35', '36'])).
% 0.66/0.84  thf('80', plain,
% 0.66/0.84      (((r2_hidden @ sk_C @ 
% 0.66/0.84         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.66/0.84        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('81', plain,
% 0.66/0.84      (((r2_hidden @ sk_C @ 
% 0.66/0.84         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('split', [status(esa)], ['80'])).
% 0.66/0.84  thf('82', plain,
% 0.66/0.84      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.66/0.84        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('clc', [status(thm)], ['43', '44'])).
% 0.66/0.84  thf('83', plain,
% 0.66/0.84      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.66/0.84         (~ (l1_orders_2 @ X12)
% 0.66/0.84          | ~ (v5_orders_2 @ X12)
% 0.66/0.84          | ~ (v4_orders_2 @ X12)
% 0.66/0.84          | ~ (v3_orders_2 @ X12)
% 0.66/0.84          | (v2_struct_0 @ X12)
% 0.66/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.66/0.84          | ((X15) = (sk_D_1 @ X13 @ X12 @ X15))
% 0.66/0.84          | ~ (r2_hidden @ X15 @ (a_2_0_orders_2 @ X12 @ X13)))),
% 0.66/0.84      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.66/0.84  thf('84', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X0 @ 
% 0.66/0.84             (a_2_0_orders_2 @ sk_A @ 
% 0.66/0.84              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.66/0.84          | ((X0)
% 0.66/0.84              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ 
% 0.66/0.84                 X0))
% 0.66/0.84          | (v2_struct_0 @ sk_A)
% 0.66/0.84          | ~ (v3_orders_2 @ sk_A)
% 0.66/0.84          | ~ (v4_orders_2 @ sk_A)
% 0.66/0.84          | ~ (v5_orders_2 @ sk_A)
% 0.66/0.84          | ~ (l1_orders_2 @ sk_A))),
% 0.66/0.84      inference('sup-', [status(thm)], ['82', '83'])).
% 0.66/0.84  thf('85', plain,
% 0.66/0.84      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.84         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.66/0.84      inference('clc', [status(thm)], ['70', '71'])).
% 0.66/0.84  thf('86', plain, ((v3_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('87', plain, ((v4_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('90', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (r2_hidden @ X0 @ 
% 0.66/0.84             (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.66/0.84          | ((X0)
% 0.66/0.84              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ 
% 0.66/0.84                 X0))
% 0.66/0.84          | (v2_struct_0 @ sk_A))),
% 0.66/0.84      inference('demod', [status(thm)], ['84', '85', '86', '87', '88', '89'])).
% 0.66/0.84  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('92', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (((X0)
% 0.66/0.84            = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ X0))
% 0.66/0.84          | ~ (r2_hidden @ X0 @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.66/0.84      inference('clc', [status(thm)], ['90', '91'])).
% 0.66/0.84  thf('93', plain,
% 0.66/0.84      ((((sk_C)
% 0.66/0.84          = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ sk_C)))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['81', '92'])).
% 0.66/0.84  thf('94', plain,
% 0.66/0.84      (((((sk_C) = (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.66/0.84         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('sup+', [status(thm)], ['79', '93'])).
% 0.66/0.84  thf('95', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.66/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.66/0.84  thf('96', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.66/0.84         (((X1) != (X0))
% 0.66/0.84          | (r2_hidden @ X1 @ X2)
% 0.66/0.84          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.66/0.84      inference('cnf', [status(esa)], [d2_tarski])).
% 0.66/0.84  thf('97', plain,
% 0.66/0.84      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.66/0.84      inference('simplify', [status(thm)], ['96'])).
% 0.66/0.84  thf('98', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.66/0.84      inference('sup+', [status(thm)], ['95', '97'])).
% 0.66/0.84  thf('99', plain,
% 0.66/0.84      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.66/0.84          = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['62', '72'])).
% 0.66/0.84  thf('100', plain,
% 0.66/0.84      (((r2_hidden @ sk_C @ 
% 0.66/0.84         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('split', [status(esa)], ['80'])).
% 0.66/0.84  thf('101', plain,
% 0.66/0.84      ((((r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('sup+', [status(thm)], ['99', '100'])).
% 0.66/0.84  thf('102', plain,
% 0.66/0.84      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.66/0.84         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['37', '45'])).
% 0.66/0.84  thf('103', plain,
% 0.66/0.84      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.66/0.84         (~ (l1_orders_2 @ X12)
% 0.66/0.84          | ~ (v5_orders_2 @ X12)
% 0.66/0.84          | ~ (v4_orders_2 @ X12)
% 0.66/0.84          | ~ (v3_orders_2 @ X12)
% 0.66/0.84          | (v2_struct_0 @ X12)
% 0.66/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.66/0.84          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.66/0.84          | (r2_orders_2 @ X12 @ X14 @ (sk_D_1 @ X13 @ X12 @ X15))
% 0.66/0.84          | ~ (r2_hidden @ X14 @ X13)
% 0.66/0.84          | ~ (r2_hidden @ X15 @ (a_2_0_orders_2 @ X12 @ X13)))),
% 0.66/0.84      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.66/0.84  thf('104', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B))
% 0.66/0.84          | (r2_orders_2 @ sk_A @ X1 @ 
% 0.66/0.84             (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.66/0.84          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | (v2_struct_0 @ sk_A)
% 0.66/0.84          | ~ (v3_orders_2 @ sk_A)
% 0.66/0.84          | ~ (v4_orders_2 @ sk_A)
% 0.66/0.84          | ~ (v5_orders_2 @ sk_A)
% 0.66/0.84          | ~ (l1_orders_2 @ sk_A))),
% 0.66/0.84      inference('sup-', [status(thm)], ['102', '103'])).
% 0.66/0.84  thf('105', plain, ((v3_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('106', plain, ((v4_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('107', plain, ((v5_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('108', plain, ((l1_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('109', plain,
% 0.66/0.84      (![X0 : $i, X1 : $i]:
% 0.66/0.84         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B))
% 0.66/0.84          | (r2_orders_2 @ sk_A @ X1 @ 
% 0.66/0.84             (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.66/0.84          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | (v2_struct_0 @ sk_A))),
% 0.66/0.84      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.66/0.84  thf('110', plain,
% 0.66/0.84      ((![X0 : $i]:
% 0.66/0.84          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84           | (v2_struct_0 @ sk_A)
% 0.66/0.84           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84           | (r2_orders_2 @ sk_A @ X0 @ 
% 0.66/0.84              (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.66/0.84           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.66/0.84           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['101', '109'])).
% 0.66/0.84  thf('111', plain,
% 0.66/0.84      ((![X0 : $i]:
% 0.66/0.84          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.66/0.84           | (r2_orders_2 @ sk_A @ X0 @ 
% 0.66/0.84              (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.66/0.84           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84           | (v2_struct_0 @ sk_A)
% 0.66/0.84           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('simplify', [status(thm)], ['110'])).
% 0.66/0.84  thf('112', plain,
% 0.66/0.84      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84         | (v2_struct_0 @ sk_A)
% 0.66/0.84         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.66/0.84         | (r2_orders_2 @ sk_A @ sk_B @ 
% 0.66/0.84            (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['98', '111'])).
% 0.66/0.84  thf('113', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('114', plain,
% 0.66/0.84      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84         | (v2_struct_0 @ sk_A)
% 0.66/0.84         | (r2_orders_2 @ sk_A @ sk_B @ 
% 0.66/0.84            (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('demod', [status(thm)], ['112', '113'])).
% 0.66/0.84  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('116', plain,
% 0.66/0.84      ((((r2_orders_2 @ sk_A @ sk_B @ 
% 0.66/0.84          (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.66/0.84         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('clc', [status(thm)], ['114', '115'])).
% 0.66/0.84  thf('117', plain,
% 0.66/0.84      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.66/0.84         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('sup+', [status(thm)], ['94', '116'])).
% 0.66/0.84  thf('118', plain,
% 0.66/0.84      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.66/0.84         <= (((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('simplify', [status(thm)], ['117'])).
% 0.66/0.84  thf('119', plain,
% 0.66/0.84      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.66/0.84         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.66/0.84      inference('split', [status(esa)], ['74'])).
% 0.66/0.84  thf('120', plain,
% 0.66/0.84      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.66/0.84         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.66/0.84             ((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['118', '119'])).
% 0.66/0.84  thf('121', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['31', '32'])).
% 0.66/0.84  thf('122', plain,
% 0.66/0.84      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))
% 0.66/0.84         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.66/0.84             ((r2_hidden @ sk_C @ 
% 0.66/0.84               (k1_orders_2 @ sk_A @ 
% 0.66/0.84                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['120', '121'])).
% 0.66/0.84  thf('123', plain,
% 0.66/0.84      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.66/0.84       ~
% 0.66/0.84       ((r2_hidden @ sk_C @ 
% 0.66/0.84         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.66/0.84      inference('sup-', [status(thm)], ['78', '122'])).
% 0.66/0.84  thf('124', plain,
% 0.66/0.84      (~
% 0.66/0.84       ((r2_hidden @ sk_C @ 
% 0.66/0.84         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.66/0.84      inference('sat_resolution*', [status(thm)], ['77', '123'])).
% 0.66/0.84  thf('125', plain,
% 0.66/0.84      ((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('simpl_trail', [status(thm)], ['76', '124'])).
% 0.66/0.84  thf('126', plain,
% 0.66/0.84      ((((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B))
% 0.66/0.84        | (v2_struct_0 @ sk_A)
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['61', '125'])).
% 0.66/0.84  thf('127', plain,
% 0.66/0.84      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84        | (v2_struct_0 @ sk_A)
% 0.66/0.84        | ((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B)))),
% 0.66/0.84      inference('simplify', [status(thm)], ['126'])).
% 0.66/0.84  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('129', plain,
% 0.66/0.84      ((((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('clc', [status(thm)], ['127', '128'])).
% 0.66/0.84  thf('130', plain,
% 0.66/0.84      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.66/0.84         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('sup+', [status(thm)], ['37', '45'])).
% 0.66/0.84  thf('131', plain,
% 0.66/0.84      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.66/0.84         (~ (l1_orders_2 @ X12)
% 0.66/0.84          | ~ (v5_orders_2 @ X12)
% 0.66/0.84          | ~ (v4_orders_2 @ X12)
% 0.66/0.84          | ~ (v3_orders_2 @ X12)
% 0.66/0.84          | (v2_struct_0 @ X12)
% 0.66/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.66/0.84          | (r2_hidden @ X15 @ (a_2_0_orders_2 @ X12 @ X13))
% 0.66/0.84          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.66/0.84          | ((X15) != (X16))
% 0.66/0.84          | ~ (r2_orders_2 @ X12 @ (sk_E @ X16 @ X13 @ X12) @ X16))),
% 0.66/0.84      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.66/0.84  thf('132', plain,
% 0.66/0.84      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.66/0.84         (~ (r2_orders_2 @ X12 @ (sk_E @ X16 @ X13 @ X12) @ X16)
% 0.66/0.84          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.66/0.84          | (r2_hidden @ X16 @ (a_2_0_orders_2 @ X12 @ X13))
% 0.66/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.66/0.84          | (v2_struct_0 @ X12)
% 0.66/0.84          | ~ (v3_orders_2 @ X12)
% 0.66/0.84          | ~ (v4_orders_2 @ X12)
% 0.66/0.84          | ~ (v5_orders_2 @ X12)
% 0.66/0.84          | ~ (l1_orders_2 @ X12))),
% 0.66/0.84      inference('simplify', [status(thm)], ['131'])).
% 0.66/0.84  thf('133', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | ~ (l1_orders_2 @ sk_A)
% 0.66/0.84          | ~ (v5_orders_2 @ sk_A)
% 0.66/0.84          | ~ (v4_orders_2 @ sk_A)
% 0.66/0.84          | ~ (v3_orders_2 @ sk_A)
% 0.66/0.84          | (v2_struct_0 @ sk_A)
% 0.66/0.84          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.66/0.84               X0))),
% 0.66/0.84      inference('sup-', [status(thm)], ['130', '132'])).
% 0.66/0.84  thf('134', plain, ((l1_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('135', plain, ((v5_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('136', plain, ((v4_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('137', plain, ((v3_orders_2 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('138', plain,
% 0.66/0.84      (![X0 : $i]:
% 0.66/0.84         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | (v2_struct_0 @ sk_A)
% 0.66/0.84          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.66/0.84               X0))),
% 0.66/0.84      inference('demod', [status(thm)], ['133', '134', '135', '136', '137'])).
% 0.66/0.84  thf('139', plain,
% 0.66/0.84      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.66/0.84        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84        | (v2_struct_0 @ sk_A)
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('sup-', [status(thm)], ['129', '138'])).
% 0.66/0.84  thf('140', plain,
% 0.66/0.84      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.66/0.84         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.66/0.84      inference('split', [status(esa)], ['80'])).
% 0.66/0.84  thf('141', plain,
% 0.66/0.84      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.66/0.84       ((r2_hidden @ sk_C @ 
% 0.66/0.84         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.66/0.84      inference('split', [status(esa)], ['80'])).
% 0.66/0.84  thf('142', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.66/0.84      inference('sat_resolution*', [status(thm)], ['77', '123', '141'])).
% 0.66/0.84  thf('143', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.66/0.84      inference('simpl_trail', [status(thm)], ['140', '142'])).
% 0.66/0.84  thf('144', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('145', plain,
% 0.66/0.84      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84        | (v2_struct_0 @ sk_A)
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('demod', [status(thm)], ['139', '143', '144'])).
% 0.66/0.84  thf('146', plain,
% 0.66/0.84      (((v2_struct_0 @ sk_A)
% 0.66/0.84        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('simplify', [status(thm)], ['145'])).
% 0.66/0.84  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.84  thf('148', plain,
% 0.66/0.84      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.66/0.84        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.66/0.84      inference('clc', [status(thm)], ['146', '147'])).
% 0.66/0.84  thf('149', plain,
% 0.66/0.84      ((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.66/0.84        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.66/0.84      inference('simpl_trail', [status(thm)], ['76', '124'])).
% 0.66/0.84  thf('150', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.66/0.84      inference('clc', [status(thm)], ['148', '149'])).
% 0.66/0.84  thf('151', plain,
% 0.66/0.84      (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A))),
% 0.66/0.84      inference('demod', [status(thm)], ['33', '150'])).
% 0.66/0.84  thf('152', plain, ($false), inference('sup-', [status(thm)], ['22', '151'])).
% 0.66/0.84  
% 0.66/0.84  % SZS output end Refutation
% 0.66/0.84  
% 0.66/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
