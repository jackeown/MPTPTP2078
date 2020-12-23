%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yqLhauHKNd

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:59 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 562 expanded)
%              Number of leaves         :   48 ( 182 expanded)
%              Depth                    :   24
%              Number of atoms          : 2255 (9574 expanded)
%              Number of equality atoms :   45 (  72 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

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

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( r1_orders_2 @ X27 @ X26 @ X26 )
      | ~ ( l1_orders_2 @ X27 )
      | ~ ( v3_orders_2 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t24_orders_2])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_orders_2 @ sk_A @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_3 @ X37 @ X38 @ X39 )
      | ~ ( r1_orders_2 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    zip_tseitin_3 @ sk_B @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ D @ A )
       => ~ ( zip_tseitin_1 @ D @ C @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('12',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_2 @ X33 @ X34 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X41 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X42 @ X40 @ X41 ) @ X42 @ X40 @ X41 )
      | ~ ( zip_tseitin_3 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X41 ) )
      | ~ ( l1_orders_2 @ X41 )
      | ~ ( v3_orders_2 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_9])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    zip_tseitin_1 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ X31 @ X32 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('24',plain,(
    r2_hidden @ sk_B @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_orders_2 @ X18 @ X17 )
        = ( a_2_1_orders_2 @ X18 @ X17 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

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

thf('44',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ( X22 != X23 )
      | ( r2_hidden @ ( sk_E @ X23 @ X20 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ( r2_hidden @ ( sk_E @ X23 @ X20 @ X19 ) @ X20 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ( r2_hidden @ X23 @ ( a_2_1_orders_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_struct_0 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('53',plain,(
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

thf('54',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('55',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('62',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( ( k6_domain_1 @ X24 @ X25 )
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('63',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
        = sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
        = sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
        = sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('71',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ( X22 != X23 )
      | ~ ( r2_orders_2 @ X19 @ X23 @ ( sk_E @ X23 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('72',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( r2_orders_2 @ X19 @ X23 @ ( sk_E @ X23 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X19 ) )
      | ( r2_hidden @ X23 @ ( a_2_1_orders_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v2_struct_0 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
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
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,
    ( ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['69','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['38','85'])).

thf('87',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('89',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    zip_tseitin_3 @ sk_B @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('91',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_2 @ X33 @ X34 @ X35 @ X36 )
      | ( zip_tseitin_0 @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( zip_tseitin_3 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    zip_tseitin_0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( zip_tseitin_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('98',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('99',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','100'])).

thf('102',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['24','101'])).

thf('103',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf('104',plain,(
    r2_hidden @ sk_B @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('105',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('106',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['39'])).

thf('107',plain,
    ( ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('110',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X22
        = ( sk_D_1 @ X20 @ X19 @ X22 ) )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['108','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['107','118'])).

thf('120',plain,
    ( ( ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('125',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['123','125'])).

thf('127',plain,
    ( ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('128',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('130',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ( r2_orders_2 @ X19 @ ( sk_D_1 @ X20 @ X19 @ X22 ) @ X21 )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('131',plain,(
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
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['128','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['127','138'])).

thf('140',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['126','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['122','145'])).

thf('147',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('149',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('151',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ sk_B @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['104','151'])).

thf('153',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','102','103','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yqLhauHKNd
% 0.17/0.37  % Computer   : n005.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 16:05:18 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 1.65/1.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.82  % Solved by: fo/fo7.sh
% 1.65/1.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.82  % done 1317 iterations in 1.345s
% 1.65/1.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.82  % SZS output start Refutation
% 1.65/1.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.82  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.65/1.82  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.65/1.82  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.82  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.65/1.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.65/1.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.65/1.82  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 1.65/1.82  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 1.65/1.82  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.82  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 1.65/1.82  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 1.65/1.82  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 1.65/1.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.65/1.82  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 1.65/1.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.65/1.82  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.65/1.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.65/1.82  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.65/1.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.65/1.82  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.65/1.82  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.65/1.82  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 1.65/1.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.82  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.65/1.82  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 1.65/1.82  thf(t52_orders_2, conjecture,
% 1.65/1.82    (![A:$i]:
% 1.65/1.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.65/1.82         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.65/1.82       ( ![B:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.65/1.82           ( ![C:$i]:
% 1.65/1.82             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.65/1.82               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 1.65/1.82                 ( r2_hidden @
% 1.65/1.82                   B @ 
% 1.65/1.82                   ( k2_orders_2 @
% 1.65/1.82                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 1.65/1.82  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.82    (~( ![A:$i]:
% 1.65/1.82        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.65/1.82            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.65/1.82          ( ![B:$i]:
% 1.65/1.82            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.65/1.82              ( ![C:$i]:
% 1.65/1.82                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.65/1.82                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 1.65/1.82                    ( r2_hidden @
% 1.65/1.82                      B @ 
% 1.65/1.82                      ( k2_orders_2 @
% 1.65/1.82                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 1.65/1.82    inference('cnf.neg', [status(esa)], [t52_orders_2])).
% 1.65/1.82  thf('0', plain,
% 1.65/1.82      ((~ (r2_hidden @ sk_B @ 
% 1.65/1.82           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.65/1.82        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('1', plain,
% 1.65/1.82      (~
% 1.65/1.82       ((r2_hidden @ sk_B @ 
% 1.65/1.82         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 1.65/1.82       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.65/1.82      inference('split', [status(esa)], ['0'])).
% 1.65/1.82  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf(t24_orders_2, axiom,
% 1.65/1.82    (![A:$i]:
% 1.65/1.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.65/1.82       ( ![B:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.65/1.82           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 1.65/1.82  thf('3', plain,
% 1.65/1.82      (![X26 : $i, X27 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 1.65/1.82          | (r1_orders_2 @ X27 @ X26 @ X26)
% 1.65/1.82          | ~ (l1_orders_2 @ X27)
% 1.65/1.82          | ~ (v3_orders_2 @ X27)
% 1.65/1.82          | (v2_struct_0 @ X27))),
% 1.65/1.82      inference('cnf', [status(esa)], [t24_orders_2])).
% 1.65/1.82  thf('4', plain,
% 1.65/1.82      (((v2_struct_0 @ sk_A)
% 1.65/1.82        | ~ (v3_orders_2 @ sk_A)
% 1.65/1.82        | ~ (l1_orders_2 @ sk_A)
% 1.65/1.82        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 1.65/1.82      inference('sup-', [status(thm)], ['2', '3'])).
% 1.65/1.82  thf('5', plain, ((v3_orders_2 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('7', plain,
% 1.65/1.82      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 1.65/1.82      inference('demod', [status(thm)], ['4', '5', '6'])).
% 1.65/1.82  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('9', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 1.65/1.82      inference('clc', [status(thm)], ['7', '8'])).
% 1.65/1.82  thf(t38_orders_2, axiom,
% 1.65/1.82    (![A:$i]:
% 1.65/1.82     ( ( ( l1_orders_2 @ A ) & ( v3_orders_2 @ A ) ) =>
% 1.65/1.82       ( ![B:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.65/1.82           ( ![C:$i]:
% 1.65/1.82             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.65/1.82               ( ( ~( ( ![D:$i]:
% 1.65/1.82                        ( ( ( m1_subset_1 @
% 1.65/1.82                              D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.65/1.82                            ( v6_orders_2 @ D @ A ) ) =>
% 1.65/1.82                          ( ~( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 1.65/1.82                      ( ( r1_orders_2 @ A @ C @ B ) | 
% 1.65/1.82                        ( r1_orders_2 @ A @ B @ C ) ) ) ) & 
% 1.65/1.82                 ( ~( ( ~( r1_orders_2 @ A @ C @ B ) ) & 
% 1.65/1.82                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 1.65/1.82                      ( ?[D:$i]:
% 1.65/1.82                        ( ( v6_orders_2 @ D @ A ) & 
% 1.65/1.82                          ( m1_subset_1 @
% 1.65/1.82                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.65/1.82                          ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 1.65/1.82  thf(zf_stmt_1, axiom,
% 1.65/1.82    (![C:$i,B:$i,A:$i]:
% 1.65/1.82     ( ( ( r1_orders_2 @ A @ B @ C ) | ( r1_orders_2 @ A @ C @ B ) ) =>
% 1.65/1.82       ( zip_tseitin_3 @ C @ B @ A ) ))).
% 1.65/1.82  thf('10', plain,
% 1.65/1.82      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.65/1.82         ((zip_tseitin_3 @ X37 @ X38 @ X39) | ~ (r1_orders_2 @ X39 @ X38 @ X37))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.65/1.82  thf('11', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 1.65/1.82      inference('sup-', [status(thm)], ['9', '10'])).
% 1.65/1.82  thf(zf_stmt_2, axiom,
% 1.65/1.82    (![D:$i,C:$i,B:$i,A:$i]:
% 1.65/1.82     ( ( ( zip_tseitin_0 @ D @ A ) => ( ~( zip_tseitin_1 @ D @ C @ B ) ) ) =>
% 1.65/1.82       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 1.65/1.82  thf('12', plain,
% 1.65/1.82      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.65/1.82         ((zip_tseitin_2 @ X33 @ X34 @ X35 @ X36)
% 1.65/1.82          | (zip_tseitin_1 @ X33 @ X34 @ X35))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.65/1.82  thf('13', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf(zf_stmt_3, type, zip_tseitin_3 : $i > $i > $i > $o).
% 1.65/1.82  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 1.65/1.82  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.65/1.82  thf(zf_stmt_6, axiom,
% 1.65/1.82    (![D:$i,C:$i,B:$i]:
% 1.65/1.82     ( ( zip_tseitin_1 @ D @ C @ B ) =>
% 1.65/1.82       ( ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ))).
% 1.65/1.82  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $o).
% 1.65/1.82  thf(zf_stmt_8, axiom,
% 1.65/1.82    (![D:$i,A:$i]:
% 1.65/1.82     ( ( zip_tseitin_0 @ D @ A ) =>
% 1.65/1.82       ( ( v6_orders_2 @ D @ A ) & 
% 1.65/1.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.65/1.82  thf(zf_stmt_9, axiom,
% 1.65/1.82    (![A:$i]:
% 1.65/1.82     ( ( ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.65/1.82       ( ![B:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.65/1.82           ( ![C:$i]:
% 1.65/1.82             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.65/1.82               ( ( ~( ( ?[D:$i]:
% 1.65/1.82                        ( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) & 
% 1.65/1.82                          ( m1_subset_1 @
% 1.65/1.82                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.65/1.82                          ( v6_orders_2 @ D @ A ) ) ) & 
% 1.65/1.82                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 1.65/1.82                      ( ~( r1_orders_2 @ A @ C @ B ) ) ) ) & 
% 1.65/1.82                 ( ~( ( zip_tseitin_3 @ C @ B @ A ) & 
% 1.65/1.82                      ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 1.65/1.82  thf('14', plain,
% 1.65/1.82      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X41))
% 1.65/1.82          | ~ (zip_tseitin_2 @ (sk_D_2 @ X42 @ X40 @ X41) @ X42 @ X40 @ X41)
% 1.65/1.82          | ~ (zip_tseitin_3 @ X42 @ X40 @ X41)
% 1.65/1.82          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X41))
% 1.65/1.82          | ~ (l1_orders_2 @ X41)
% 1.65/1.82          | ~ (v3_orders_2 @ X41))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_9])).
% 1.65/1.82  thf('15', plain,
% 1.65/1.82      (![X0 : $i]:
% 1.65/1.82         (~ (v3_orders_2 @ sk_A)
% 1.65/1.82          | ~ (l1_orders_2 @ sk_A)
% 1.65/1.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.65/1.82          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 1.65/1.82          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 1.65/1.82      inference('sup-', [status(thm)], ['13', '14'])).
% 1.65/1.82  thf('16', plain, ((v3_orders_2 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('18', plain,
% 1.65/1.82      (![X0 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.65/1.82          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 1.65/1.82          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 1.65/1.82      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.65/1.82  thf('19', plain,
% 1.65/1.82      (![X0 : $i]:
% 1.65/1.82         ((zip_tseitin_1 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B)
% 1.65/1.82          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 1.65/1.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['12', '18'])).
% 1.65/1.82  thf('20', plain,
% 1.65/1.82      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.65/1.82        | (zip_tseitin_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B))),
% 1.65/1.82      inference('sup-', [status(thm)], ['11', '19'])).
% 1.65/1.82  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('22', plain,
% 1.65/1.82      ((zip_tseitin_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B)),
% 1.65/1.82      inference('demod', [status(thm)], ['20', '21'])).
% 1.65/1.82  thf('23', plain,
% 1.65/1.82      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.65/1.82         ((r2_hidden @ X30 @ X31) | ~ (zip_tseitin_1 @ X31 @ X32 @ X30))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_6])).
% 1.65/1.82  thf('24', plain, ((r2_hidden @ sk_B @ (sk_D_2 @ sk_B @ sk_B @ sk_A))),
% 1.65/1.82      inference('sup-', [status(thm)], ['22', '23'])).
% 1.65/1.82  thf('25', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf(t2_subset, axiom,
% 1.65/1.82    (![A:$i,B:$i]:
% 1.65/1.82     ( ( m1_subset_1 @ A @ B ) =>
% 1.65/1.82       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.65/1.82  thf('26', plain,
% 1.65/1.82      (![X9 : $i, X10 : $i]:
% 1.65/1.82         ((r2_hidden @ X9 @ X10)
% 1.65/1.82          | (v1_xboole_0 @ X10)
% 1.65/1.82          | ~ (m1_subset_1 @ X9 @ X10))),
% 1.65/1.82      inference('cnf', [status(esa)], [t2_subset])).
% 1.65/1.82  thf('27', plain,
% 1.65/1.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.82        | (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('sup-', [status(thm)], ['25', '26'])).
% 1.65/1.82  thf(t63_subset_1, axiom,
% 1.65/1.82    (![A:$i,B:$i]:
% 1.65/1.82     ( ( r2_hidden @ A @ B ) =>
% 1.65/1.82       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.65/1.82  thf('28', plain,
% 1.65/1.82      (![X7 : $i, X8 : $i]:
% 1.65/1.82         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 1.65/1.82          | ~ (r2_hidden @ X7 @ X8))),
% 1.65/1.82      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.65/1.82  thf('29', plain,
% 1.65/1.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.82        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 1.65/1.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['27', '28'])).
% 1.65/1.82  thf(d13_orders_2, axiom,
% 1.65/1.82    (![A:$i]:
% 1.65/1.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.65/1.82         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.65/1.82       ( ![B:$i]:
% 1.65/1.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.65/1.82           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 1.65/1.82  thf('30', plain,
% 1.65/1.82      (![X17 : $i, X18 : $i]:
% 1.65/1.82         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.65/1.82          | ((k2_orders_2 @ X18 @ X17) = (a_2_1_orders_2 @ X18 @ X17))
% 1.65/1.82          | ~ (l1_orders_2 @ X18)
% 1.65/1.82          | ~ (v5_orders_2 @ X18)
% 1.65/1.82          | ~ (v4_orders_2 @ X18)
% 1.65/1.82          | ~ (v3_orders_2 @ X18)
% 1.65/1.82          | (v2_struct_0 @ X18))),
% 1.65/1.82      inference('cnf', [status(esa)], [d13_orders_2])).
% 1.65/1.82  thf('31', plain,
% 1.65/1.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.82        | (v2_struct_0 @ sk_A)
% 1.65/1.82        | ~ (v3_orders_2 @ sk_A)
% 1.65/1.82        | ~ (v4_orders_2 @ sk_A)
% 1.65/1.82        | ~ (v5_orders_2 @ sk_A)
% 1.65/1.82        | ~ (l1_orders_2 @ sk_A)
% 1.65/1.82        | ((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 1.65/1.82            = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['29', '30'])).
% 1.65/1.82  thf('32', plain, ((v3_orders_2 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('33', plain, ((v4_orders_2 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('36', plain,
% 1.65/1.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.82        | (v2_struct_0 @ sk_A)
% 1.65/1.82        | ((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 1.65/1.82            = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 1.65/1.82      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 1.65/1.82  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('38', plain,
% 1.65/1.82      ((((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 1.65/1.82          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('clc', [status(thm)], ['36', '37'])).
% 1.65/1.82  thf('39', plain,
% 1.65/1.82      (((r2_hidden @ sk_B @ 
% 1.65/1.82         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.65/1.82        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('40', plain,
% 1.65/1.82      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 1.65/1.82         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.65/1.82      inference('split', [status(esa)], ['39'])).
% 1.65/1.82  thf('41', plain,
% 1.65/1.82      ((((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 1.65/1.82          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.82        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.82      inference('clc', [status(thm)], ['36', '37'])).
% 1.65/1.82  thf('42', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.65/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.82  thf('43', plain,
% 1.65/1.82      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.82        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 1.65/1.82           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.65/1.82      inference('sup-', [status(thm)], ['27', '28'])).
% 1.65/1.82  thf(fraenkel_a_2_1_orders_2, axiom,
% 1.65/1.82    (![A:$i,B:$i,C:$i]:
% 1.65/1.82     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 1.65/1.82         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 1.65/1.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 1.65/1.82       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 1.65/1.82         ( ?[D:$i]:
% 1.65/1.82           ( ( ![E:$i]:
% 1.65/1.82               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.65/1.82                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 1.65/1.82             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.65/1.82  thf('44', plain,
% 1.65/1.82      (![X19 : $i, X20 : $i, X22 : $i, X23 : $i]:
% 1.65/1.82         (~ (l1_orders_2 @ X19)
% 1.65/1.82          | ~ (v5_orders_2 @ X19)
% 1.65/1.82          | ~ (v4_orders_2 @ X19)
% 1.65/1.82          | ~ (v3_orders_2 @ X19)
% 1.65/1.82          | (v2_struct_0 @ X19)
% 1.65/1.82          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.65/1.82          | (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20))
% 1.65/1.82          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 1.65/1.82          | ((X22) != (X23))
% 1.65/1.82          | (r2_hidden @ (sk_E @ X23 @ X20 @ X19) @ X20))),
% 1.65/1.82      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.65/1.82  thf('45', plain,
% 1.65/1.82      (![X19 : $i, X20 : $i, X23 : $i]:
% 1.65/1.82         ((r2_hidden @ (sk_E @ X23 @ X20 @ X19) @ X20)
% 1.65/1.82          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 1.65/1.82          | (r2_hidden @ X23 @ (a_2_1_orders_2 @ X19 @ X20))
% 1.65/1.82          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.65/1.82          | (v2_struct_0 @ X19)
% 1.65/1.82          | ~ (v3_orders_2 @ X19)
% 1.65/1.82          | ~ (v4_orders_2 @ X19)
% 1.65/1.82          | ~ (v5_orders_2 @ X19)
% 1.65/1.82          | ~ (l1_orders_2 @ X19))),
% 1.65/1.82      inference('simplify', [status(thm)], ['44'])).
% 1.65/1.82  thf('46', plain,
% 1.65/1.82      (![X0 : $i]:
% 1.65/1.82         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.82          | ~ (l1_orders_2 @ sk_A)
% 1.65/1.82          | ~ (v5_orders_2 @ sk_A)
% 1.65/1.82          | ~ (v4_orders_2 @ sk_A)
% 1.65/1.82          | ~ (v3_orders_2 @ sk_A)
% 1.65/1.82          | (v2_struct_0 @ sk_A)
% 1.65/1.82          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.82          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A) @ 
% 1.65/1.83             (k1_tarski @ sk_C)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['43', '45'])).
% 1.65/1.83  thf('47', plain, ((l1_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('48', plain, ((v5_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('49', plain, ((v4_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('50', plain, ((v3_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('51', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | (v2_struct_0 @ sk_A)
% 1.65/1.83          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A) @ 
% 1.65/1.83             (k1_tarski @ sk_C)))),
% 1.65/1.83      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 1.65/1.83  thf('52', plain,
% 1.65/1.83      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 1.65/1.83         (k1_tarski @ sk_C))
% 1.65/1.83        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83        | (v2_struct_0 @ sk_A)
% 1.65/1.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['42', '51'])).
% 1.65/1.83  thf(t69_enumset1, axiom,
% 1.65/1.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.65/1.83  thf('53', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.65/1.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.65/1.83  thf(d2_tarski, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.65/1.83       ( ![D:$i]:
% 1.65/1.83         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.65/1.83  thf('54', plain,
% 1.65/1.83      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X4 @ X2)
% 1.65/1.83          | ((X4) = (X3))
% 1.65/1.83          | ((X4) = (X0))
% 1.65/1.83          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [d2_tarski])).
% 1.65/1.83  thf('55', plain,
% 1.65/1.83      (![X0 : $i, X3 : $i, X4 : $i]:
% 1.65/1.83         (((X4) = (X0))
% 1.65/1.83          | ((X4) = (X3))
% 1.65/1.83          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 1.65/1.83      inference('simplify', [status(thm)], ['54'])).
% 1.65/1.83  thf('56', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['53', '55'])).
% 1.65/1.83  thf('57', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.65/1.83      inference('simplify', [status(thm)], ['56'])).
% 1.65/1.83  thf('58', plain,
% 1.65/1.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83        | (v2_struct_0 @ sk_A)
% 1.65/1.83        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['52', '57'])).
% 1.65/1.83  thf('59', plain,
% 1.65/1.83      (((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 1.65/1.83        | (v2_struct_0 @ sk_A)
% 1.65/1.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['41', '58'])).
% 1.65/1.83  thf('60', plain,
% 1.65/1.83      (((v2_struct_0 @ sk_A)
% 1.65/1.83        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 1.65/1.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83        | (r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['59'])).
% 1.65/1.83  thf('61', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf(redefinition_k6_domain_1, axiom,
% 1.65/1.83    (![A:$i,B:$i]:
% 1.65/1.83     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.65/1.83       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.65/1.83  thf('62', plain,
% 1.65/1.83      (![X24 : $i, X25 : $i]:
% 1.65/1.83         ((v1_xboole_0 @ X24)
% 1.65/1.83          | ~ (m1_subset_1 @ X25 @ X24)
% 1.65/1.83          | ((k6_domain_1 @ X24 @ X25) = (k1_tarski @ X25)))),
% 1.65/1.83      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.65/1.83  thf('63', plain,
% 1.65/1.83      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 1.65/1.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['61', '62'])).
% 1.65/1.83  thf('64', plain,
% 1.65/1.83      ((~ (r2_hidden @ sk_B @ 
% 1.65/1.83           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('split', [status(esa)], ['0'])).
% 1.65/1.83  thf('65', plain,
% 1.65/1.83      (((~ (r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.83  thf('66', plain,
% 1.65/1.83      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 1.65/1.83         | (v2_struct_0 @ sk_A)
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['60', '65'])).
% 1.65/1.83  thf('67', plain,
% 1.65/1.83      ((((v2_struct_0 @ sk_A)
% 1.65/1.83         | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['66'])).
% 1.65/1.83  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('69', plain,
% 1.65/1.83      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('clc', [status(thm)], ['67', '68'])).
% 1.65/1.83  thf('70', plain,
% 1.65/1.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 1.65/1.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['27', '28'])).
% 1.65/1.83  thf('71', plain,
% 1.65/1.83      (![X19 : $i, X20 : $i, X22 : $i, X23 : $i]:
% 1.65/1.83         (~ (l1_orders_2 @ X19)
% 1.65/1.83          | ~ (v5_orders_2 @ X19)
% 1.65/1.83          | ~ (v4_orders_2 @ X19)
% 1.65/1.83          | ~ (v3_orders_2 @ X19)
% 1.65/1.83          | (v2_struct_0 @ X19)
% 1.65/1.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.65/1.83          | (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20))
% 1.65/1.83          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 1.65/1.83          | ((X22) != (X23))
% 1.65/1.83          | ~ (r2_orders_2 @ X19 @ X23 @ (sk_E @ X23 @ X20 @ X19)))),
% 1.65/1.83      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.65/1.83  thf('72', plain,
% 1.65/1.83      (![X19 : $i, X20 : $i, X23 : $i]:
% 1.65/1.83         (~ (r2_orders_2 @ X19 @ X23 @ (sk_E @ X23 @ X20 @ X19))
% 1.65/1.83          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X19))
% 1.65/1.83          | (r2_hidden @ X23 @ (a_2_1_orders_2 @ X19 @ X20))
% 1.65/1.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.65/1.83          | (v2_struct_0 @ X19)
% 1.65/1.83          | ~ (v3_orders_2 @ X19)
% 1.65/1.83          | ~ (v4_orders_2 @ X19)
% 1.65/1.83          | ~ (v5_orders_2 @ X19)
% 1.65/1.83          | ~ (l1_orders_2 @ X19))),
% 1.65/1.83      inference('simplify', [status(thm)], ['71'])).
% 1.65/1.83  thf('73', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (l1_orders_2 @ sk_A)
% 1.65/1.83          | ~ (v5_orders_2 @ sk_A)
% 1.65/1.83          | ~ (v4_orders_2 @ sk_A)
% 1.65/1.83          | ~ (v3_orders_2 @ sk_A)
% 1.65/1.83          | (v2_struct_0 @ sk_A)
% 1.65/1.83          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 1.65/1.83               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['70', '72'])).
% 1.65/1.83  thf('74', plain, ((l1_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('75', plain, ((v5_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('76', plain, ((v4_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('77', plain, ((v3_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('78', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | (v2_struct_0 @ sk_A)
% 1.65/1.83          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 1.65/1.83               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 1.65/1.83      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 1.65/1.83  thf('79', plain,
% 1.65/1.83      (((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83         | (v2_struct_0 @ sk_A)
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['69', '78'])).
% 1.65/1.83  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('81', plain,
% 1.65/1.83      (((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83         | (v2_struct_0 @ sk_A)
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('demod', [status(thm)], ['79', '80'])).
% 1.65/1.83  thf('82', plain,
% 1.65/1.83      ((((v2_struct_0 @ sk_A)
% 1.65/1.83         | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['81'])).
% 1.65/1.83  thf('83', plain,
% 1.65/1.83      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83         | (v2_struct_0 @ sk_A)))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 1.65/1.83             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['40', '82'])).
% 1.65/1.83  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('85', plain,
% 1.65/1.83      ((((r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 1.65/1.83             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.65/1.83      inference('clc', [status(thm)], ['83', '84'])).
% 1.65/1.83  thf('86', plain,
% 1.65/1.83      ((((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 1.65/1.83             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.65/1.83      inference('sup+', [status(thm)], ['38', '85'])).
% 1.65/1.83  thf('87', plain,
% 1.65/1.83      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 1.65/1.83             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.65/1.83      inference('simplify', [status(thm)], ['86'])).
% 1.65/1.83  thf('88', plain,
% 1.65/1.83      (((~ (r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.83  thf('89', plain,
% 1.65/1.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 1.65/1.83             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.65/1.83      inference('clc', [status(thm)], ['87', '88'])).
% 1.65/1.83  thf('90', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 1.65/1.83      inference('sup-', [status(thm)], ['9', '10'])).
% 1.65/1.83  thf('91', plain,
% 1.65/1.83      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.65/1.83         ((zip_tseitin_2 @ X33 @ X34 @ X35 @ X36) | (zip_tseitin_0 @ X33 @ X36))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.65/1.83  thf('92', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 1.65/1.83          | ~ (zip_tseitin_2 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.65/1.83  thf('93', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((zip_tseitin_0 @ (sk_D_2 @ X0 @ sk_B @ sk_A) @ sk_A)
% 1.65/1.83          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 1.65/1.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['91', '92'])).
% 1.65/1.83  thf('94', plain,
% 1.65/1.83      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.65/1.83        | (zip_tseitin_0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['90', '93'])).
% 1.65/1.83  thf('95', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('96', plain, ((zip_tseitin_0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 1.65/1.83      inference('demod', [status(thm)], ['94', '95'])).
% 1.65/1.83  thf('97', plain,
% 1.65/1.83      (![X28 : $i, X29 : $i]:
% 1.65/1.83         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.65/1.83          | ~ (zip_tseitin_0 @ X28 @ X29))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.65/1.83  thf('98', plain,
% 1.65/1.83      ((m1_subset_1 @ (sk_D_2 @ sk_B @ sk_B @ sk_A) @ 
% 1.65/1.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['96', '97'])).
% 1.65/1.83  thf(t5_subset, axiom,
% 1.65/1.83    (![A:$i,B:$i,C:$i]:
% 1.65/1.83     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.65/1.83          ( v1_xboole_0 @ C ) ) ))).
% 1.65/1.83  thf('99', plain,
% 1.65/1.83      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X14 @ X15)
% 1.65/1.83          | ~ (v1_xboole_0 @ X16)
% 1.65/1.83          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.65/1.83      inference('cnf', [status(esa)], [t5_subset])).
% 1.65/1.83  thf('100', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['98', '99'])).
% 1.65/1.83  thf('101', plain,
% 1.65/1.83      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))
% 1.65/1.83         <= (~
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 1.65/1.83             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['89', '100'])).
% 1.65/1.83  thf('102', plain,
% 1.65/1.83      (((r2_hidden @ sk_B @ 
% 1.65/1.83         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 1.65/1.83       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.65/1.83      inference('sup-', [status(thm)], ['24', '101'])).
% 1.65/1.83  thf('103', plain,
% 1.65/1.83      (((r2_hidden @ sk_B @ 
% 1.65/1.83         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 1.65/1.83       ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.65/1.83      inference('split', [status(esa)], ['39'])).
% 1.65/1.83  thf('104', plain, ((r2_hidden @ sk_B @ (sk_D_2 @ sk_B @ sk_B @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['22', '23'])).
% 1.65/1.83  thf('105', plain,
% 1.65/1.83      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 1.65/1.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['61', '62'])).
% 1.65/1.83  thf('106', plain,
% 1.65/1.83      (((r2_hidden @ sk_B @ 
% 1.65/1.83         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('split', [status(esa)], ['39'])).
% 1.65/1.83  thf('107', plain,
% 1.65/1.83      ((((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['105', '106'])).
% 1.65/1.83  thf('108', plain,
% 1.65/1.83      ((((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 1.65/1.83          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('clc', [status(thm)], ['36', '37'])).
% 1.65/1.83  thf('109', plain,
% 1.65/1.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 1.65/1.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['27', '28'])).
% 1.65/1.83  thf('110', plain,
% 1.65/1.83      (![X19 : $i, X20 : $i, X22 : $i]:
% 1.65/1.83         (~ (l1_orders_2 @ X19)
% 1.65/1.83          | ~ (v5_orders_2 @ X19)
% 1.65/1.83          | ~ (v4_orders_2 @ X19)
% 1.65/1.83          | ~ (v3_orders_2 @ X19)
% 1.65/1.83          | (v2_struct_0 @ X19)
% 1.65/1.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.65/1.83          | ((X22) = (sk_D_1 @ X20 @ X19 @ X22))
% 1.65/1.83          | ~ (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20)))),
% 1.65/1.83      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.65/1.83  thf('111', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83          | ((X0) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0))
% 1.65/1.83          | (v2_struct_0 @ sk_A)
% 1.65/1.83          | ~ (v3_orders_2 @ sk_A)
% 1.65/1.83          | ~ (v4_orders_2 @ sk_A)
% 1.65/1.83          | ~ (v5_orders_2 @ sk_A)
% 1.65/1.83          | ~ (l1_orders_2 @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['109', '110'])).
% 1.65/1.83  thf('112', plain, ((v3_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('113', plain, ((v4_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('114', plain, ((v5_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('115', plain, ((l1_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('116', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83          | ((X0) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0))
% 1.65/1.83          | (v2_struct_0 @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['111', '112', '113', '114', '115'])).
% 1.65/1.83  thf('117', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | (v2_struct_0 @ sk_A)
% 1.65/1.83          | ((X0) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0))
% 1.65/1.83          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['108', '116'])).
% 1.65/1.83  thf('118', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (((X0) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0))
% 1.65/1.83          | (v2_struct_0 @ sk_A)
% 1.65/1.83          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['117'])).
% 1.65/1.83  thf('119', plain,
% 1.65/1.83      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (v2_struct_0 @ sk_A)
% 1.65/1.83         | ((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['107', '118'])).
% 1.65/1.83  thf('120', plain,
% 1.65/1.83      (((((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))
% 1.65/1.83         | (v2_struct_0 @ sk_A)
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['119'])).
% 1.65/1.83  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('122', plain,
% 1.65/1.83      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | ((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('clc', [status(thm)], ['120', '121'])).
% 1.65/1.83  thf('123', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.65/1.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.65/1.83  thf('124', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.65/1.83         (((X1) != (X0))
% 1.65/1.83          | (r2_hidden @ X1 @ X2)
% 1.65/1.83          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 1.65/1.83      inference('cnf', [status(esa)], [d2_tarski])).
% 1.65/1.83  thf('125', plain,
% 1.65/1.83      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 1.65/1.83      inference('simplify', [status(thm)], ['124'])).
% 1.65/1.83  thf('126', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.65/1.83      inference('sup+', [status(thm)], ['123', '125'])).
% 1.65/1.83  thf('127', plain,
% 1.65/1.83      ((((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['105', '106'])).
% 1.65/1.83  thf('128', plain,
% 1.65/1.83      ((((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 1.65/1.83          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('clc', [status(thm)], ['36', '37'])).
% 1.65/1.83  thf('129', plain,
% 1.65/1.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 1.65/1.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['27', '28'])).
% 1.65/1.83  thf('130', plain,
% 1.65/1.83      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.65/1.83         (~ (l1_orders_2 @ X19)
% 1.65/1.83          | ~ (v5_orders_2 @ X19)
% 1.65/1.83          | ~ (v4_orders_2 @ X19)
% 1.65/1.83          | ~ (v3_orders_2 @ X19)
% 1.65/1.83          | (v2_struct_0 @ X19)
% 1.65/1.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.65/1.83          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 1.65/1.83          | (r2_orders_2 @ X19 @ (sk_D_1 @ X20 @ X19 @ X22) @ X21)
% 1.65/1.83          | ~ (r2_hidden @ X21 @ X20)
% 1.65/1.83          | ~ (r2_hidden @ X22 @ (a_2_1_orders_2 @ X19 @ X20)))),
% 1.65/1.83      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.65/1.83  thf('131', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 1.65/1.83          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 1.65/1.83             X1)
% 1.65/1.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | (v2_struct_0 @ sk_A)
% 1.65/1.83          | ~ (v3_orders_2 @ sk_A)
% 1.65/1.83          | ~ (v4_orders_2 @ sk_A)
% 1.65/1.83          | ~ (v5_orders_2 @ sk_A)
% 1.65/1.83          | ~ (l1_orders_2 @ sk_A))),
% 1.65/1.83      inference('sup-', [status(thm)], ['129', '130'])).
% 1.65/1.83  thf('132', plain, ((v3_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('133', plain, ((v4_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('134', plain, ((v5_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('135', plain, ((l1_orders_2 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('136', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 1.65/1.83          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 1.65/1.83             X1)
% 1.65/1.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | (v2_struct_0 @ sk_A))),
% 1.65/1.83      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 1.65/1.83  thf('137', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.65/1.83          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | (v2_struct_0 @ sk_A)
% 1.65/1.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 1.65/1.83             X1)
% 1.65/1.83          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 1.65/1.83          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['128', '136'])).
% 1.65/1.83  thf('138', plain,
% 1.65/1.83      (![X0 : $i, X1 : $i]:
% 1.65/1.83         (~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 1.65/1.83          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 1.65/1.83             X1)
% 1.65/1.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | (v2_struct_0 @ sk_A)
% 1.65/1.83          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['137'])).
% 1.65/1.83  thf('139', plain,
% 1.65/1.83      ((![X0 : $i]:
% 1.65/1.83          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83           | (v2_struct_0 @ sk_A)
% 1.65/1.83           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83           | (r2_orders_2 @ sk_A @ 
% 1.65/1.83              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 1.65/1.83           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['127', '138'])).
% 1.65/1.83  thf('140', plain,
% 1.65/1.83      ((![X0 : $i]:
% 1.65/1.83          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 1.65/1.83           | (r2_orders_2 @ sk_A @ 
% 1.65/1.83              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 1.65/1.83           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83           | (v2_struct_0 @ sk_A)
% 1.65/1.83           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['139'])).
% 1.65/1.83  thf('141', plain,
% 1.65/1.83      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (v2_struct_0 @ sk_A)
% 1.65/1.83         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 1.65/1.83            sk_C)))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['126', '140'])).
% 1.65/1.83  thf('142', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('143', plain,
% 1.65/1.83      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (v2_struct_0 @ sk_A)
% 1.65/1.83         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 1.65/1.83            sk_C)))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('demod', [status(thm)], ['141', '142'])).
% 1.65/1.83  thf('144', plain, (~ (v2_struct_0 @ sk_A)),
% 1.65/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.83  thf('145', plain,
% 1.65/1.83      ((((r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 1.65/1.83          sk_C)
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('clc', [status(thm)], ['143', '144'])).
% 1.65/1.83  thf('146', plain,
% 1.65/1.83      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup+', [status(thm)], ['122', '145'])).
% 1.65/1.83  thf('147', plain,
% 1.65/1.83      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 1.65/1.83         <= (((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('simplify', [status(thm)], ['146'])).
% 1.65/1.83  thf('148', plain,
% 1.65/1.83      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 1.65/1.83         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.65/1.83      inference('split', [status(esa)], ['0'])).
% 1.65/1.83  thf('149', plain,
% 1.65/1.83      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.65/1.83         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['147', '148'])).
% 1.65/1.83  thf('150', plain,
% 1.65/1.83      (![X0 : $i]:
% 1.65/1.83         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.65/1.83          | ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))),
% 1.65/1.83      inference('sup-', [status(thm)], ['98', '99'])).
% 1.65/1.83  thf('151', plain,
% 1.65/1.83      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_2 @ sk_B @ sk_B @ sk_A)))
% 1.65/1.83         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 1.65/1.83             ((r2_hidden @ sk_B @ 
% 1.65/1.83               (k2_orders_2 @ sk_A @ 
% 1.65/1.83                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.65/1.83      inference('sup-', [status(thm)], ['149', '150'])).
% 1.65/1.83  thf('152', plain,
% 1.65/1.83      (~
% 1.65/1.83       ((r2_hidden @ sk_B @ 
% 1.65/1.83         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 1.65/1.83       ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.65/1.83      inference('sup-', [status(thm)], ['104', '151'])).
% 1.65/1.83  thf('153', plain, ($false),
% 1.65/1.83      inference('sat_resolution*', [status(thm)], ['1', '102', '103', '152'])).
% 1.65/1.83  
% 1.65/1.83  % SZS output end Refutation
% 1.65/1.83  
% 1.67/1.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
