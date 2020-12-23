%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Acsdq2wJNQ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:57 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  196 (1104 expanded)
%              Number of leaves         :   47 ( 330 expanded)
%              Depth                    :   31
%              Number of atoms          : 1994 (19529 expanded)
%              Number of equality atoms :   41 ( 170 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( r1_orders_2 @ X25 @ X24 @ X24 )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_3 @ X35 @ X36 @ X37 )
      | ~ ( r1_orders_2 @ X37 @ X36 @ X35 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_2 @ X31 @ X32 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X31 @ X32 @ X33 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X39 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X40 @ X38 @ X39 ) @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_3 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 )
      | ~ ( v3_orders_2 @ X39 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X29 @ X30 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    zip_tseitin_3 @ sk_B @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_2 @ X31 @ X32 @ X33 @ X34 )
      | ( zip_tseitin_0 @ X31 @ X34 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( zip_tseitin_0 @ X26 @ X27 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('37',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

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

thf('43',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r2_hidden @ X20 @ ( a_2_0_orders_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X17 ) )
      | ( X20 != X21 )
      | ( r2_hidden @ ( sk_E @ X21 @ X18 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('44',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( r2_hidden @ ( sk_E @ X21 @ X18 @ X17 ) @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ X21 @ ( a_2_0_orders_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_struct_0 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
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
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','50'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('52',plain,(
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

thf('53',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('54',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

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

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k1_orders_2 @ X14 @ X13 )
        = ( a_2_0_orders_2 @ X14 @ X13 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d12_orders_2])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['71'])).

thf('75',plain,(
    r2_hidden @ sk_B @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('77',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ( ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('81',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( X20
        = ( sk_D_1 @ X18 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ ( a_2_0_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_C
        = ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,
    ( ( ( sk_C
        = ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C
        = ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('94',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','94'])).

thf('96',plain,
    ( ( ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','78'])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('98',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r2_orders_2 @ X17 @ X19 @ ( sk_D_1 @ X18 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( a_2_0_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('99',plain,(
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
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','104'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['95','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['91','111'])).

thf('113',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['71'])).

thf('115',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('117',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','117'])).

thf('119',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['74','118'])).

thf('120',plain,
    ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['73','119'])).

thf('121',plain,
    ( ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','120'])).

thf('122',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('126',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r2_hidden @ X20 @ ( a_2_0_orders_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X17 ) )
      | ( X20 != X21 )
      | ~ ( r2_orders_2 @ X17 @ ( sk_E @ X21 @ X18 @ X17 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('127',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ~ ( r2_orders_2 @ X17 @ ( sk_E @ X21 @ X18 @ X17 ) @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ X21 @ ( a_2_0_orders_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_struct_0 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
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
    inference('sup-',[status(thm)],['125','127'])).

thf('129',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf('134',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','133'])).

thf('135',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['77'])).

thf('136',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['77'])).

thf('137',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['74','118','136'])).

thf('138',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['135','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','138','139'])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['73','119'])).

thf('145',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','145'])).

thf('147',plain,(
    $false ),
    inference('sup-',[status(thm)],['22','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Acsdq2wJNQ
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:56:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.33  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 595 iterations in 0.360s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.78  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.59/0.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.78  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.59/0.78  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.59/0.78  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 0.59/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.78  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.59/0.78  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.59/0.78  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.78  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.59/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.78  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.59/0.78  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.59/0.78  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.59/0.78  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.78  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.59/0.78  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.59/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.59/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.78  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.59/0.78  thf(t51_orders_2, conjecture,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.78         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78           ( ![C:$i]:
% 0.59/0.78             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.59/0.78                 ( r2_hidden @
% 0.59/0.78                   C @ 
% 0.59/0.78                   ( k1_orders_2 @
% 0.59/0.78                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i]:
% 0.59/0.78        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.78            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.78          ( ![B:$i]:
% 0.59/0.78            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78              ( ![C:$i]:
% 0.59/0.78                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.59/0.78                    ( r2_hidden @
% 0.59/0.78                      C @ 
% 0.59/0.78                      ( k1_orders_2 @
% 0.59/0.78                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t51_orders_2])).
% 0.59/0.78  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(t24_orders_2, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.59/0.78  thf('1', plain,
% 0.59/0.78      (![X24 : $i, X25 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.59/0.78          | (r1_orders_2 @ X25 @ X24 @ X24)
% 0.59/0.78          | ~ (l1_orders_2 @ X25)
% 0.59/0.78          | ~ (v3_orders_2 @ X25)
% 0.59/0.78          | (v2_struct_0 @ X25))),
% 0.59/0.78      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_A)
% 0.59/0.78        | ~ (v3_orders_2 @ sk_A)
% 0.59/0.78        | ~ (l1_orders_2 @ sk_A)
% 0.59/0.78        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.78  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.59/0.78      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.59/0.78  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('7', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.59/0.78      inference('clc', [status(thm)], ['5', '6'])).
% 0.59/0.78  thf(t38_orders_2, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( l1_orders_2 @ A ) & ( v3_orders_2 @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78           ( ![C:$i]:
% 0.59/0.78             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78               ( ( ~( ( ![D:$i]:
% 0.59/0.78                        ( ( ( m1_subset_1 @
% 0.59/0.78                              D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.59/0.78                            ( v6_orders_2 @ D @ A ) ) =>
% 0.59/0.78                          ( ~( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.59/0.78                      ( ( r1_orders_2 @ A @ C @ B ) | 
% 0.59/0.78                        ( r1_orders_2 @ A @ B @ C ) ) ) ) & 
% 0.59/0.78                 ( ~( ( ~( r1_orders_2 @ A @ C @ B ) ) & 
% 0.59/0.78                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.59/0.78                      ( ?[D:$i]:
% 0.59/0.78                        ( ( v6_orders_2 @ D @ A ) & 
% 0.59/0.78                          ( m1_subset_1 @
% 0.59/0.78                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.59/0.78                          ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_1, axiom,
% 0.59/0.78    (![C:$i,B:$i,A:$i]:
% 0.59/0.78     ( ( ( r1_orders_2 @ A @ B @ C ) | ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.59/0.78       ( zip_tseitin_3 @ C @ B @ A ) ))).
% 0.59/0.78  thf('8', plain,
% 0.59/0.78      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.59/0.78         ((zip_tseitin_3 @ X35 @ X36 @ X37) | ~ (r1_orders_2 @ X37 @ X36 @ X35))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.78  thf('9', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 0.59/0.78      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.78  thf(zf_stmt_2, axiom,
% 0.59/0.78    (![D:$i,C:$i,B:$i,A:$i]:
% 0.59/0.78     ( ( ( zip_tseitin_0 @ D @ A ) => ( ~( zip_tseitin_1 @ D @ C @ B ) ) ) =>
% 0.59/0.78       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.59/0.78  thf('10', plain,
% 0.59/0.78      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.78         ((zip_tseitin_2 @ X31 @ X32 @ X33 @ X34)
% 0.59/0.78          | (zip_tseitin_1 @ X31 @ X32 @ X33))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.78  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(zf_stmt_3, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.59/0.78  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.59/0.78  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.59/0.78  thf(zf_stmt_6, axiom,
% 0.59/0.78    (![D:$i,C:$i,B:$i]:
% 0.59/0.78     ( ( zip_tseitin_1 @ D @ C @ B ) =>
% 0.59/0.78       ( ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ))).
% 0.59/0.78  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $o).
% 0.59/0.78  thf(zf_stmt_8, axiom,
% 0.59/0.78    (![D:$i,A:$i]:
% 0.59/0.78     ( ( zip_tseitin_0 @ D @ A ) =>
% 0.59/0.78       ( ( v6_orders_2 @ D @ A ) & 
% 0.59/0.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_9, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78           ( ![C:$i]:
% 0.59/0.78             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.78               ( ( ~( ( ?[D:$i]:
% 0.59/0.78                        ( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) & 
% 0.59/0.78                          ( m1_subset_1 @
% 0.59/0.78                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.59/0.78                          ( v6_orders_2 @ D @ A ) ) ) & 
% 0.59/0.78                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.59/0.78                      ( ~( r1_orders_2 @ A @ C @ B ) ) ) ) & 
% 0.59/0.78                 ( ~( ( zip_tseitin_3 @ C @ B @ A ) & 
% 0.59/0.78                      ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.78  thf('12', plain,
% 0.59/0.78      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X39))
% 0.59/0.78          | ~ (zip_tseitin_2 @ (sk_D_2 @ X40 @ X38 @ X39) @ X40 @ X38 @ X39)
% 0.59/0.78          | ~ (zip_tseitin_3 @ X40 @ X38 @ X39)
% 0.59/0.78          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 0.59/0.78          | ~ (l1_orders_2 @ X39)
% 0.59/0.78          | ~ (v3_orders_2 @ X39))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.59/0.78  thf('13', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v3_orders_2 @ sk_A)
% 0.59/0.78          | ~ (l1_orders_2 @ sk_A)
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.59/0.78          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.78  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.59/0.78          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.59/0.78  thf('17', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((zip_tseitin_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B)
% 0.59/0.78          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['10', '16'])).
% 0.59/0.78  thf('18', plain,
% 0.59/0.78      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (zip_tseitin_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B))),
% 0.59/0.78      inference('sup-', [status(thm)], ['9', '17'])).
% 0.59/0.78  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      ((zip_tseitin_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B)),
% 0.59/0.78      inference('demod', [status(thm)], ['18', '19'])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.78         ((r2_hidden @ X28 @ X29) | ~ (zip_tseitin_1 @ X29 @ X30 @ X28))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.59/0.78  thf('22', plain, ((r2_hidden @ sk_B @ (sk_D_2 @ sk_B @ sk_B @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.78  thf('23', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 0.59/0.78      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.78         ((zip_tseitin_2 @ X31 @ X32 @ X33 @ X34) | (zip_tseitin_0 @ X31 @ X34))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.59/0.78          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.59/0.78  thf('26', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((zip_tseitin_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.59/0.78          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.78  thf('27', plain,
% 0.59/0.78      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (zip_tseitin_0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['23', '26'])).
% 0.59/0.78  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('29', plain, ((zip_tseitin_0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 0.59/0.78      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.78  thf('30', plain,
% 0.59/0.78      (![X26 : $i, X27 : $i]:
% 0.59/0.78         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.59/0.78          | ~ (zip_tseitin_0 @ X26 @ X27))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      ((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ 
% 0.59/0.78        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['29', '30'])).
% 0.59/0.78  thf(t5_subset, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.59/0.78          ( v1_xboole_0 @ C ) ) ))).
% 0.59/0.78  thf('32', plain,
% 0.59/0.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X10 @ X11)
% 0.59/0.78          | ~ (v1_xboole_0 @ X12)
% 0.59/0.78          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t5_subset])).
% 0.59/0.78  thf('33', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.78  thf('34', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('35', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(redefinition_k6_domain_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.59/0.78       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.59/0.78  thf('36', plain,
% 0.59/0.78      (![X22 : $i, X23 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ X22)
% 0.59/0.78          | ~ (m1_subset_1 @ X23 @ X22)
% 0.59/0.78          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.59/0.78  thf('37', plain,
% 0.59/0.78      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.78  thf('38', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(dt_k6_domain_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.59/0.78       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.59/0.78  thf('39', plain,
% 0.59/0.78      (![X15 : $i, X16 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ X15)
% 0.59/0.78          | ~ (m1_subset_1 @ X16 @ X15)
% 0.59/0.78          | (m1_subset_1 @ (k6_domain_1 @ X15 @ X16) @ (k1_zfmisc_1 @ X15)))),
% 0.59/0.78      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.59/0.78  thf('40', plain,
% 0.59/0.78      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.59/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.59/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup+', [status(thm)], ['37', '40'])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.59/0.78  thf(fraenkel_a_2_0_orders_2, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.59/0.78         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.59/0.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.59/0.78       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 0.59/0.78         ( ?[D:$i]:
% 0.59/0.78           ( ( ![E:$i]:
% 0.59/0.78               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.59/0.78                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 0.59/0.78             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.59/0.78  thf('43', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.59/0.78         (~ (l1_orders_2 @ X17)
% 0.59/0.78          | ~ (v5_orders_2 @ X17)
% 0.59/0.78          | ~ (v4_orders_2 @ X17)
% 0.59/0.78          | ~ (v3_orders_2 @ X17)
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.59/0.78          | (r2_hidden @ X20 @ (a_2_0_orders_2 @ X17 @ X18))
% 0.59/0.78          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X17))
% 0.59/0.78          | ((X20) != (X21))
% 0.59/0.78          | (r2_hidden @ (sk_E @ X21 @ X18 @ X17) @ X18))),
% 0.59/0.78      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.59/0.78  thf('44', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.59/0.78         ((r2_hidden @ (sk_E @ X21 @ X18 @ X17) @ X18)
% 0.59/0.78          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X17))
% 0.59/0.78          | (r2_hidden @ X21 @ (a_2_0_orders_2 @ X17 @ X18))
% 0.59/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (v3_orders_2 @ X17)
% 0.59/0.78          | ~ (v4_orders_2 @ X17)
% 0.59/0.78          | ~ (v5_orders_2 @ X17)
% 0.59/0.78          | ~ (l1_orders_2 @ X17))),
% 0.59/0.78      inference('simplify', [status(thm)], ['43'])).
% 0.59/0.78  thf('45', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (l1_orders_2 @ sk_A)
% 0.59/0.78          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.78          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.78          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ sk_A)
% 0.59/0.78          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.78             (k1_tarski @ sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['42', '44'])).
% 0.59/0.78  thf('46', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('47', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('48', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('49', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('50', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | (v2_struct_0 @ sk_A)
% 0.59/0.78          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.78             (k1_tarski @ sk_B)))),
% 0.59/0.78      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.59/0.78  thf('51', plain,
% 0.59/0.78      (((r2_hidden @ (sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.78         (k1_tarski @ sk_B))
% 0.59/0.78        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['34', '50'])).
% 0.59/0.78  thf(t69_enumset1, axiom,
% 0.59/0.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.78  thf('52', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.59/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.78  thf(d2_tarski, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.59/0.78       ( ![D:$i]:
% 0.59/0.78         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.59/0.78  thf('53', plain,
% 0.59/0.78      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X4 @ X2)
% 0.59/0.78          | ((X4) = (X3))
% 0.59/0.78          | ((X4) = (X0))
% 0.59/0.78          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_tarski])).
% 0.59/0.78  thf('54', plain,
% 0.59/0.78      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.59/0.78         (((X4) = (X0))
% 0.59/0.78          | ((X4) = (X3))
% 0.59/0.78          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['53'])).
% 0.59/0.78  thf('55', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['52', '54'])).
% 0.59/0.78  thf('56', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['55'])).
% 0.59/0.78  thf('57', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78        | ((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['51', '56'])).
% 0.59/0.78  thf('58', plain,
% 0.59/0.78      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.59/0.78  thf('59', plain,
% 0.59/0.78      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.59/0.78         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.78  thf(d12_orders_2, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.78         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.78       ( ![B:$i]:
% 0.59/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.78           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 0.59/0.78  thf('60', plain,
% 0.59/0.78      (![X13 : $i, X14 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.59/0.78          | ((k1_orders_2 @ X14 @ X13) = (a_2_0_orders_2 @ X14 @ X13))
% 0.59/0.78          | ~ (l1_orders_2 @ X14)
% 0.59/0.78          | ~ (v5_orders_2 @ X14)
% 0.59/0.78          | ~ (v4_orders_2 @ X14)
% 0.59/0.78          | ~ (v3_orders_2 @ X14)
% 0.59/0.78          | (v2_struct_0 @ X14))),
% 0.59/0.78      inference('cnf', [status(esa)], [d12_orders_2])).
% 0.59/0.78  thf('61', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | ~ (v3_orders_2 @ sk_A)
% 0.59/0.78        | ~ (v4_orders_2 @ sk_A)
% 0.59/0.78        | ~ (v5_orders_2 @ sk_A)
% 0.59/0.78        | ~ (l1_orders_2 @ sk_A)
% 0.59/0.78        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.78            = (a_2_0_orders_2 @ sk_A @ 
% 0.59/0.78               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['59', '60'])).
% 0.59/0.78  thf('62', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('63', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('64', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('66', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.78            = (a_2_0_orders_2 @ sk_A @ 
% 0.59/0.78               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.78      inference('demod', [status(thm)], ['61', '62', '63', '64', '65'])).
% 0.59/0.78  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('68', plain,
% 0.59/0.78      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.78          = (a_2_0_orders_2 @ sk_A @ 
% 0.59/0.78             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('clc', [status(thm)], ['66', '67'])).
% 0.59/0.78  thf('69', plain,
% 0.59/0.78      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.78          = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup+', [status(thm)], ['58', '68'])).
% 0.59/0.78  thf('70', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.78            = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['69'])).
% 0.59/0.78  thf('71', plain,
% 0.59/0.78      ((~ (r2_hidden @ sk_C @ 
% 0.59/0.78           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.59/0.78        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('72', plain,
% 0.59/0.78      ((~ (r2_hidden @ sk_C @ 
% 0.59/0.78           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.59/0.78         <= (~
% 0.59/0.78             ((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('split', [status(esa)], ['71'])).
% 0.59/0.78  thf('73', plain,
% 0.59/0.78      (((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.78         <= (~
% 0.59/0.78             ((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['70', '72'])).
% 0.59/0.78  thf('74', plain,
% 0.59/0.78      (~
% 0.59/0.78       ((r2_hidden @ sk_C @ 
% 0.59/0.78         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))) | 
% 0.59/0.78       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.59/0.78      inference('split', [status(esa)], ['71'])).
% 0.59/0.78  thf('75', plain, ((r2_hidden @ sk_B @ (sk_D_2 @ sk_B @ sk_B @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.59/0.78  thf('76', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.78            = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['69'])).
% 0.59/0.78  thf('77', plain,
% 0.59/0.78      (((r2_hidden @ sk_C @ 
% 0.59/0.78         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.59/0.78        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('78', plain,
% 0.59/0.78      (((r2_hidden @ sk_C @ 
% 0.59/0.78         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('split', [status(esa)], ['77'])).
% 0.59/0.78  thf('79', plain,
% 0.59/0.78      ((((r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['76', '78'])).
% 0.59/0.78  thf('80', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.59/0.78  thf('81', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.59/0.78         (~ (l1_orders_2 @ X17)
% 0.59/0.78          | ~ (v5_orders_2 @ X17)
% 0.59/0.78          | ~ (v4_orders_2 @ X17)
% 0.59/0.78          | ~ (v3_orders_2 @ X17)
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.59/0.78          | ((X20) = (sk_D_1 @ X18 @ X17 @ X20))
% 0.59/0.78          | ~ (r2_hidden @ X20 @ (a_2_0_orders_2 @ X17 @ X18)))),
% 0.59/0.78      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.59/0.78  thf('82', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78          | ((X0) = (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.59/0.78          | (v2_struct_0 @ sk_A)
% 0.59/0.78          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.78          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.78          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.78          | ~ (l1_orders_2 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['80', '81'])).
% 0.59/0.78  thf('83', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('84', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('85', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('86', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('87', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78          | ((X0) = (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.59/0.78          | (v2_struct_0 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.59/0.78  thf('88', plain,
% 0.59/0.78      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | ((sk_C) = (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['79', '87'])).
% 0.59/0.78  thf('89', plain,
% 0.59/0.78      (((((sk_C) = (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['88'])).
% 0.59/0.78  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('91', plain,
% 0.59/0.78      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78         | ((sk_C) = (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('clc', [status(thm)], ['89', '90'])).
% 0.59/0.78  thf('92', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.59/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.78  thf('93', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.78         (((X1) != (X0))
% 0.59/0.78          | (r2_hidden @ X1 @ X2)
% 0.59/0.78          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [d2_tarski])).
% 0.59/0.78  thf('94', plain,
% 0.59/0.78      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['93'])).
% 0.59/0.78  thf('95', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['92', '94'])).
% 0.59/0.78  thf('96', plain,
% 0.59/0.78      ((((r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['76', '78'])).
% 0.59/0.78  thf('97', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.59/0.78  thf('98', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.78         (~ (l1_orders_2 @ X17)
% 0.59/0.78          | ~ (v5_orders_2 @ X17)
% 0.59/0.78          | ~ (v4_orders_2 @ X17)
% 0.59/0.78          | ~ (v3_orders_2 @ X17)
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.59/0.78          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.59/0.78          | (r2_orders_2 @ X17 @ X19 @ (sk_D_1 @ X18 @ X17 @ X20))
% 0.59/0.78          | ~ (r2_hidden @ X19 @ X18)
% 0.59/0.78          | ~ (r2_hidden @ X20 @ (a_2_0_orders_2 @ X17 @ X18)))),
% 0.59/0.78      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.59/0.78  thf('99', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B))
% 0.59/0.78          | (r2_orders_2 @ sk_A @ X1 @ 
% 0.59/0.78             (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.59/0.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | (v2_struct_0 @ sk_A)
% 0.59/0.78          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.78          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.78          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.78          | ~ (l1_orders_2 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['97', '98'])).
% 0.59/0.78  thf('100', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('101', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('102', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('103', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('104', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B))
% 0.59/0.78          | (r2_orders_2 @ sk_A @ X1 @ 
% 0.59/0.78             (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.59/0.78          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | (v2_struct_0 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.59/0.78  thf('105', plain,
% 0.59/0.78      ((![X0 : $i]:
% 0.59/0.78          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78           | (v2_struct_0 @ sk_A)
% 0.59/0.78           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78           | (r2_orders_2 @ sk_A @ X0 @ 
% 0.59/0.78              (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.59/0.78           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.59/0.78           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['96', '104'])).
% 0.59/0.78  thf('106', plain,
% 0.59/0.78      ((![X0 : $i]:
% 0.59/0.78          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.59/0.78           | (r2_orders_2 @ sk_A @ X0 @ 
% 0.59/0.78              (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.59/0.78           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78           | (v2_struct_0 @ sk_A)
% 0.59/0.78           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['105'])).
% 0.59/0.78  thf('107', plain,
% 0.59/0.78      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.59/0.78         | (r2_orders_2 @ sk_A @ sk_B @ 
% 0.59/0.78            (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['95', '106'])).
% 0.59/0.78  thf('108', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('109', plain,
% 0.59/0.78      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78         | (v2_struct_0 @ sk_A)
% 0.59/0.78         | (r2_orders_2 @ sk_A @ sk_B @ 
% 0.59/0.78            (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('demod', [status(thm)], ['107', '108'])).
% 0.59/0.78  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('111', plain,
% 0.59/0.78      ((((r2_orders_2 @ sk_A @ sk_B @ 
% 0.59/0.78          (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('clc', [status(thm)], ['109', '110'])).
% 0.59/0.78  thf('112', plain,
% 0.59/0.78      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('sup+', [status(thm)], ['91', '111'])).
% 0.59/0.78  thf('113', plain,
% 0.59/0.78      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.59/0.78         <= (((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['112'])).
% 0.59/0.78  thf('114', plain,
% 0.59/0.78      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('split', [status(esa)], ['71'])).
% 0.59/0.78  thf('115', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.59/0.78         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.59/0.78             ((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['113', '114'])).
% 0.59/0.78  thf('116', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.78  thf('117', plain,
% 0.59/0.78      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))
% 0.59/0.78         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.59/0.78             ((r2_hidden @ sk_C @ 
% 0.59/0.78               (k1_orders_2 @ sk_A @ 
% 0.59/0.78                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['115', '116'])).
% 0.59/0.78  thf('118', plain,
% 0.59/0.78      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.59/0.78       ~
% 0.59/0.78       ((r2_hidden @ sk_C @ 
% 0.59/0.78         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['75', '117'])).
% 0.59/0.78  thf('119', plain,
% 0.59/0.78      (~
% 0.59/0.78       ((r2_hidden @ sk_C @ 
% 0.59/0.78         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['74', '118'])).
% 0.59/0.78  thf('120', plain,
% 0.59/0.78      ((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['73', '119'])).
% 0.59/0.78  thf('121', plain,
% 0.59/0.78      ((((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['57', '120'])).
% 0.59/0.78  thf('122', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | ((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['121'])).
% 0.59/0.78  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('124', plain,
% 0.59/0.78      ((((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('clc', [status(thm)], ['122', '123'])).
% 0.59/0.78  thf('125', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.59/0.78           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.59/0.78  thf('126', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.59/0.78         (~ (l1_orders_2 @ X17)
% 0.59/0.78          | ~ (v5_orders_2 @ X17)
% 0.59/0.78          | ~ (v4_orders_2 @ X17)
% 0.59/0.78          | ~ (v3_orders_2 @ X17)
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.59/0.78          | (r2_hidden @ X20 @ (a_2_0_orders_2 @ X17 @ X18))
% 0.59/0.78          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X17))
% 0.59/0.78          | ((X20) != (X21))
% 0.59/0.78          | ~ (r2_orders_2 @ X17 @ (sk_E @ X21 @ X18 @ X17) @ X21))),
% 0.59/0.78      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.59/0.78  thf('127', plain,
% 0.59/0.78      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.59/0.78         (~ (r2_orders_2 @ X17 @ (sk_E @ X21 @ X18 @ X17) @ X21)
% 0.59/0.78          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X17))
% 0.59/0.78          | (r2_hidden @ X21 @ (a_2_0_orders_2 @ X17 @ X18))
% 0.59/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.59/0.78          | (v2_struct_0 @ X17)
% 0.59/0.78          | ~ (v3_orders_2 @ X17)
% 0.59/0.78          | ~ (v4_orders_2 @ X17)
% 0.59/0.78          | ~ (v5_orders_2 @ X17)
% 0.59/0.78          | ~ (l1_orders_2 @ X17))),
% 0.59/0.78      inference('simplify', [status(thm)], ['126'])).
% 0.59/0.78  thf('128', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (l1_orders_2 @ sk_A)
% 0.59/0.78          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.78          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.78          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.78          | (v2_struct_0 @ sk_A)
% 0.59/0.78          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.78               X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['125', '127'])).
% 0.59/0.78  thf('129', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('130', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('131', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('132', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('133', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | (v2_struct_0 @ sk_A)
% 0.59/0.78          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.78               X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 0.59/0.78  thf('134', plain,
% 0.59/0.78      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['124', '133'])).
% 0.59/0.78  thf('135', plain,
% 0.59/0.78      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.59/0.78         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.78      inference('split', [status(esa)], ['77'])).
% 0.59/0.78  thf('136', plain,
% 0.59/0.78      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.59/0.78       ((r2_hidden @ sk_C @ 
% 0.59/0.78         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.78      inference('split', [status(esa)], ['77'])).
% 0.59/0.78  thf('137', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['74', '118', '136'])).
% 0.59/0.78  thf('138', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['135', '137'])).
% 0.59/0.78  thf('139', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('140', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78        | (v2_struct_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['134', '138', '139'])).
% 0.59/0.78  thf('141', plain,
% 0.59/0.78      (((v2_struct_0 @ sk_A)
% 0.59/0.78        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['140'])).
% 0.59/0.78  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('143', plain,
% 0.59/0.78      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.78        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.59/0.78      inference('clc', [status(thm)], ['141', '142'])).
% 0.59/0.78  thf('144', plain,
% 0.59/0.78      ((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.78        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['73', '119'])).
% 0.59/0.78  thf('145', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.59/0.78      inference('clc', [status(thm)], ['143', '144'])).
% 0.59/0.78  thf('146', plain,
% 0.59/0.78      (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['33', '145'])).
% 0.59/0.78  thf('147', plain, ($false), inference('sup-', [status(thm)], ['22', '146'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
