%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FeWrhdIIS7

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:50 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 172 expanded)
%              Number of leaves         :   42 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  794 (2035 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t48_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_orders_2])).

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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r1_orders_2 @ X22 @ X21 @ X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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
      | ~ ( zip_tseitin_2 @ ( sk_D_1 @ X37 @ X35 @ X36 ) @ X37 @ X35 @ X36 )
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X26 @ X27 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( sk_D_1 @ sk_B @ sk_B @ sk_A ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( zip_tseitin_0 @ X23 @ X24 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('36',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X9 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t47_orders_2,axiom,(
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
                  & ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X40 ) )
      | ~ ( r2_hidden @ X39 @ ( k1_orders_2 @ X40 @ X41 ) )
      | ~ ( r2_hidden @ X39 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_orders_2 @ X40 )
      | ~ ( v5_orders_2 @ X40 )
      | ~ ( v4_orders_2 @ X40 )
      | ~ ( v3_orders_2 @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t47_orders_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('55',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( sk_D_1 @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','60'])).

thf('62',plain,(
    $false ),
    inference('sup-',[status(thm)],['22','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FeWrhdIIS7
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:04:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 177 iterations in 0.084s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.55  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.35/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.35/0.55  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.35/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.55  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.35/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.35/0.55  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.35/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.55  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.35/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.35/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(t48_orders_2, conjecture,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ~( r2_hidden @
% 0.35/0.55                B @ 
% 0.35/0.55                ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i]:
% 0.35/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.55            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.55          ( ![B:$i]:
% 0.35/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55              ( ~( r2_hidden @
% 0.35/0.55                   B @ 
% 0.35/0.55                   ( k1_orders_2 @
% 0.35/0.55                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t48_orders_2])).
% 0.35/0.55  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t24_orders_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (![X21 : $i, X22 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.35/0.55          | (r1_orders_2 @ X22 @ X21 @ X21)
% 0.35/0.55          | ~ (l1_orders_2 @ X22)
% 0.35/0.55          | ~ (v3_orders_2 @ X22)
% 0.35/0.55          | (v2_struct_0 @ X22))),
% 0.35/0.55      inference('cnf', [status(esa)], [t24_orders_2])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (v3_orders_2 @ sk_A)
% 0.35/0.55        | ~ (l1_orders_2 @ sk_A)
% 0.35/0.55        | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.55  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A) | (r1_orders_2 @ sk_A @ sk_B @ sk_B))),
% 0.35/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.35/0.55  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('7', plain, ((r1_orders_2 @ sk_A @ sk_B @ sk_B)),
% 0.35/0.55      inference('clc', [status(thm)], ['5', '6'])).
% 0.35/0.55  thf(t38_orders_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( l1_orders_2 @ A ) & ( v3_orders_2 @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55               ( ( ~( ( ![D:$i]:
% 0.35/0.55                        ( ( ( m1_subset_1 @
% 0.35/0.55                              D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.35/0.55                            ( v6_orders_2 @ D @ A ) ) =>
% 0.35/0.55                          ( ~( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.35/0.55                      ( ( r1_orders_2 @ A @ C @ B ) | 
% 0.35/0.55                        ( r1_orders_2 @ A @ B @ C ) ) ) ) & 
% 0.35/0.55                 ( ~( ( ~( r1_orders_2 @ A @ C @ B ) ) & 
% 0.35/0.55                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.35/0.55                      ( ?[D:$i]:
% 0.35/0.55                        ( ( v6_orders_2 @ D @ A ) & 
% 0.35/0.55                          ( m1_subset_1 @
% 0.35/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.35/0.55                          ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_1, axiom,
% 0.35/0.55    (![C:$i,B:$i,A:$i]:
% 0.35/0.55     ( ( ( r1_orders_2 @ A @ B @ C ) | ( r1_orders_2 @ A @ C @ B ) ) =>
% 0.35/0.55       ( zip_tseitin_3 @ C @ B @ A ) ))).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.35/0.55         ((zip_tseitin_3 @ X32 @ X33 @ X34) | ~ (r1_orders_2 @ X34 @ X33 @ X32))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.55  thf('9', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 0.35/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.55  thf(zf_stmt_2, axiom,
% 0.35/0.55    (![D:$i,C:$i,B:$i,A:$i]:
% 0.35/0.55     ( ( ( zip_tseitin_0 @ D @ A ) => ( ~( zip_tseitin_1 @ D @ C @ B ) ) ) =>
% 0.35/0.55       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.35/0.55         ((zip_tseitin_2 @ X28 @ X29 @ X30 @ X31)
% 0.35/0.55          | (zip_tseitin_1 @ X28 @ X29 @ X30))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.55  thf('11', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(zf_stmt_3, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.35/0.55  thf(zf_stmt_4, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.35/0.55  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.55  thf(zf_stmt_6, axiom,
% 0.35/0.55    (![D:$i,C:$i,B:$i]:
% 0.35/0.55     ( ( zip_tseitin_1 @ D @ C @ B ) =>
% 0.35/0.55       ( ( r2_hidden @ B @ D ) & ( r2_hidden @ C @ D ) ) ))).
% 0.35/0.55  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.55  thf(zf_stmt_8, axiom,
% 0.35/0.55    (![D:$i,A:$i]:
% 0.35/0.55     ( ( zip_tseitin_0 @ D @ A ) =>
% 0.35/0.55       ( ( v6_orders_2 @ D @ A ) & 
% 0.35/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_9, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55               ( ( ~( ( ?[D:$i]:
% 0.35/0.55                        ( ( r2_hidden @ C @ D ) & ( r2_hidden @ B @ D ) & 
% 0.35/0.55                          ( m1_subset_1 @
% 0.35/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.35/0.55                          ( v6_orders_2 @ D @ A ) ) ) & 
% 0.35/0.55                      ( ~( r1_orders_2 @ A @ B @ C ) ) & 
% 0.35/0.55                      ( ~( r1_orders_2 @ A @ C @ B ) ) ) ) & 
% 0.35/0.55                 ( ~( ( zip_tseitin_3 @ C @ B @ A ) & 
% 0.35/0.55                      ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 0.35/0.55          | ~ (zip_tseitin_2 @ (sk_D_1 @ X37 @ X35 @ X36) @ X37 @ X35 @ X36)
% 0.35/0.55          | ~ (zip_tseitin_3 @ X37 @ X35 @ X36)
% 0.35/0.55          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.35/0.55          | ~ (l1_orders_2 @ X36)
% 0.35/0.55          | ~ (v3_orders_2 @ X36))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_9])).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (v3_orders_2 @ sk_A)
% 0.35/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.35/0.55          | ~ (zip_tseitin_2 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.55  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.35/0.55          | ~ (zip_tseitin_2 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((zip_tseitin_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B)
% 0.35/0.55          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['10', '16'])).
% 0.35/0.55  thf('18', plain,
% 0.35/0.55      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (zip_tseitin_1 @ (sk_D_1 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B))),
% 0.35/0.55      inference('sup-', [status(thm)], ['9', '17'])).
% 0.35/0.55  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      ((zip_tseitin_1 @ (sk_D_1 @ sk_B @ sk_B @ sk_A) @ sk_B @ sk_B)),
% 0.35/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.35/0.55         ((r2_hidden @ X25 @ X26) | ~ (zip_tseitin_1 @ X26 @ X27 @ X25))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.35/0.55  thf('22', plain, ((r2_hidden @ sk_B @ (sk_D_1 @ sk_B @ sk_B @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.55  thf('23', plain, ((zip_tseitin_3 @ sk_B @ sk_B @ sk_A)),
% 0.35/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.35/0.55         ((zip_tseitin_2 @ X28 @ X29 @ X30 @ X31) | (zip_tseitin_0 @ X28 @ X31))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.35/0.55          | ~ (zip_tseitin_2 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ X0 @ sk_B @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((zip_tseitin_0 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.35/0.55          | ~ (zip_tseitin_3 @ X0 @ sk_B @ sk_A)
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.55  thf('27', plain,
% 0.35/0.55      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (zip_tseitin_0 @ (sk_D_1 @ sk_B @ sk_B @ sk_A) @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['23', '26'])).
% 0.35/0.55  thf('28', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('29', plain, ((zip_tseitin_0 @ (sk_D_1 @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 0.35/0.55      inference('demod', [status(thm)], ['27', '28'])).
% 0.35/0.55  thf('30', plain,
% 0.35/0.55      (![X23 : $i, X24 : $i]:
% 0.35/0.55         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.35/0.55          | ~ (zip_tseitin_0 @ X23 @ X24))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.35/0.55  thf('31', plain,
% 0.35/0.55      ((m1_subset_1 @ (sk_D_1 @ sk_B @ sk_B @ sk_A) @ 
% 0.35/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.55  thf(t5_subset, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.35/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.55         (~ (r2_hidden @ X16 @ X17)
% 0.35/0.55          | ~ (v1_xboole_0 @ X18)
% 0.35/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.35/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (sk_D_1 @ sk_B @ sk_B @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.55  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k6_domain_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.55       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      (![X19 : $i, X20 : $i]:
% 0.35/0.55         ((v1_xboole_0 @ X19)
% 0.35/0.55          | ~ (m1_subset_1 @ X20 @ X19)
% 0.35/0.55          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.35/0.55  thf('36', plain,
% 0.35/0.55      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      ((r2_hidden @ sk_B @ 
% 0.35/0.55        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      (((r2_hidden @ sk_B @ (k1_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['36', '37'])).
% 0.35/0.55  thf('39', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t2_subset, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      (![X11 : $i, X12 : $i]:
% 0.35/0.55         ((r2_hidden @ X11 @ X12)
% 0.35/0.55          | (v1_xboole_0 @ X12)
% 0.35/0.55          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.35/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.55  thf(t63_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( r2_hidden @ A @ B ) =>
% 0.35/0.55       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      (![X9 : $i, X10 : $i]:
% 0.35/0.55         ((m1_subset_1 @ (k1_tarski @ X9) @ (k1_zfmisc_1 @ X10))
% 0.35/0.55          | ~ (r2_hidden @ X9 @ X10))),
% 0.35/0.55      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.35/0.55  thf('43', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.35/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.35/0.55  thf(t47_orders_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.35/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ![C:$i]:
% 0.35/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55               ( ~( ( r2_hidden @ B @ C ) & 
% 0.35/0.55                    ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('44', plain,
% 0.35/0.55      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X40))
% 0.35/0.55          | ~ (r2_hidden @ X39 @ (k1_orders_2 @ X40 @ X41))
% 0.35/0.55          | ~ (r2_hidden @ X39 @ X41)
% 0.35/0.55          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.35/0.55          | ~ (l1_orders_2 @ X40)
% 0.35/0.55          | ~ (v5_orders_2 @ X40)
% 0.35/0.55          | ~ (v4_orders_2 @ X40)
% 0.35/0.55          | ~ (v3_orders_2 @ X40)
% 0.35/0.55          | (v2_struct_0 @ X40))),
% 0.35/0.55      inference('cnf', [status(esa)], [t47_orders_2])).
% 0.35/0.55  thf('45', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55          | (v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (v3_orders_2 @ sk_A)
% 0.35/0.55          | ~ (v4_orders_2 @ sk_A)
% 0.35/0.55          | ~ (v5_orders_2 @ sk_A)
% 0.35/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.55  thf('46', plain, ((v3_orders_2 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('47', plain, ((v4_orders_2 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('48', plain, ((v5_orders_2 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('50', plain,
% 0.35/0.55      (![X0 : $i]:
% 0.35/0.55         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55          | (v2_struct_0 @ sk_A)
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.35/0.55          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.35/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.35/0.55  thf('51', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | ~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.35/0.55        | (v2_struct_0 @ sk_A)
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['38', '50'])).
% 0.35/0.55  thf('52', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t69_enumset1, axiom,
% 0.35/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.55  thf('53', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.35/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.55  thf(d2_tarski, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.35/0.55       ( ![D:$i]:
% 0.35/0.55         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.35/0.55  thf('54', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.35/0.55         (((X1) != (X0))
% 0.35/0.55          | (r2_hidden @ X1 @ X2)
% 0.35/0.55          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.35/0.55      inference('cnf', [status(esa)], [d2_tarski])).
% 0.35/0.55  thf('55', plain,
% 0.35/0.55      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.35/0.55      inference('simplify', [status(thm)], ['54'])).
% 0.35/0.55  thf('56', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.35/0.55      inference('sup+', [status(thm)], ['53', '55'])).
% 0.35/0.55  thf('57', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (v2_struct_0 @ sk_A)
% 0.35/0.55        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['51', '52', '56'])).
% 0.35/0.55  thf('58', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('simplify', [status(thm)], ['57'])).
% 0.35/0.55  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('60', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('clc', [status(thm)], ['58', '59'])).
% 0.35/0.55  thf('61', plain,
% 0.35/0.55      (![X0 : $i]: ~ (r2_hidden @ X0 @ (sk_D_1 @ sk_B @ sk_B @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['33', '60'])).
% 0.35/0.55  thf('62', plain, ($false), inference('sup-', [status(thm)], ['22', '61'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
