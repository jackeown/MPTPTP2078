%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QZkShs0As1

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 209 expanded)
%              Number of leaves         :   37 (  78 expanded)
%              Depth                    :   23
%              Number of atoms          : 1046 (3001 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   23 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k4_waybel_9_type,type,(
    k4_waybel_9: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k1_toler_1_type,type,(
    k1_toler_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t13_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_waybel_9])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ~ ( l1_waybel_0 @ X10 @ X9 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('3',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X8 ) ) )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_waybel_9,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( v6_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A )
        & ( l1_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_waybel_0 @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ( v6_waybel_0 @ ( k4_waybel_9 @ X27 @ X26 @ X28 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d7_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ( l1_waybel_0 @ B @ A )
            & ~ ( v2_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ! [D: $i] :
                  ( ( ( l1_waybel_0 @ D @ A )
                    & ( v6_waybel_0 @ D @ A ) )
                 => ( ( D
                      = ( k4_waybel_9 @ A @ B @ C ) )
                  <=> ( ( ( u1_waybel_0 @ A @ D )
                        = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) )
                      & ( r2_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) @ ( k1_toler_1 @ ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) )
                      & ! [E: $i] :
                          ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) )
                        <=> ? [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                              & ( F = E )
                              & ( r1_orders_2 @ B @ C @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B )
    <=> ( ( r1_orders_2 @ B @ C @ F )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ! [D: $i] :
                  ( ( ( v6_waybel_0 @ D @ A )
                    & ( l1_waybel_0 @ D @ A ) )
                 => ( ( D
                      = ( k4_waybel_9 @ A @ B @ C ) )
                  <=> ( ! [E: $i] :
                          ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) )
                        <=> ? [F: $i] :
                              ( zip_tseitin_0 @ F @ E @ C @ B ) )
                      & ( r2_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) @ ( k1_toler_1 @ ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) )
                      & ( ( u1_waybel_0 @ A @ D )
                        = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X25: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ~ ( v6_waybel_0 @ X20 @ X19 )
      | ~ ( l1_waybel_0 @ X20 @ X19 )
      | ( X20
       != ( k4_waybel_9 @ X19 @ X18 @ X21 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X25 @ X21 @ X18 ) @ X25 @ X21 @ X18 )
      | ~ ( r2_hidden @ X25 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X18: $i,X19: $i,X21: $i,X25: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_hidden @ X25 @ ( u1_struct_0 @ ( k4_waybel_9 @ X19 @ X18 @ X21 ) ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X25 @ X21 @ X18 ) @ X25 @ X21 @ X18 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X19 @ X18 @ X21 ) @ X19 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X19 @ X18 @ X21 ) @ X19 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ X2 @ X1 @ X0 ) ) @ X3 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X2 @ X1 @ X0 ) @ X2 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X2 @ X1 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X3 @ ( u1_struct_0 @ ( k4_waybel_9 @ X2 @ X1 @ X0 ) ) ) @ X0 @ X1 ) @ ( sk_C @ X3 @ ( u1_struct_0 @ ( k4_waybel_9 @ X2 @ X1 @ X0 ) ) ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_waybel_0 @ X26 @ X27 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ( l1_waybel_0 @ ( k4_waybel_9 @ X27 @ X26 @ X28 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25','36','37'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15 = X16 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
        = ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24','25','36','37'])).

thf('42',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ~ ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ ( u1_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['7','56'])).

thf(fc15_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ~ ( v1_xboole_0 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X11 )
      | ~ ( v1_xboole_0 @ ( u1_waybel_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc15_yellow_6])).

thf('59',plain,
    ( ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QZkShs0As1
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 65 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.50  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.21/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.50  thf(k4_waybel_9_type, type, k4_waybel_9: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.21/0.50  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k1_toler_1_type, type, k1_toler_1: $i > $i > $i).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(t13_waybel_9, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50               ( r1_tarski @
% 0.21/0.50                 ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.21/0.50                 ( u1_struct_0 @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                  ( r1_tarski @
% 0.21/0.50                    ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.21/0.50                    ( u1_struct_0 @ B ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t13_waybel_9])).
% 0.21/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_u1_waybel_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.21/0.50         ( v1_funct_2 @
% 0.21/0.50           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50         ( m1_subset_1 @
% 0.21/0.50           ( u1_waybel_0 @ A @ B ) @ 
% 0.21/0.50           ( k1_zfmisc_1 @
% 0.21/0.50             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X9)
% 0.21/0.50          | ~ (l1_waybel_0 @ X10 @ X9)
% 0.21/0.50          | (m1_subset_1 @ (u1_waybel_0 @ X9 @ X10) @ 
% 0.21/0.50             (k1_zfmisc_1 @ 
% 0.21/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X9)))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.50         (k1_zfmisc_1 @ 
% 0.21/0.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf(cc3_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50           ( v1_xboole_0 @ C ) ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ X6)
% 0.21/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X8)))
% 0.21/0.50          | (v1_xboole_0 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_waybel_0 @ sk_A @ sk_B))
% 0.21/0.50        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k4_waybel_9, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.50         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.50       ( ( v6_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) & 
% 0.21/0.50         ( l1_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.50         (~ (l1_waybel_0 @ X26 @ X27)
% 0.21/0.50          | (v2_struct_0 @ X26)
% 0.21/0.50          | ~ (l1_struct_0 @ X27)
% 0.21/0.50          | (v2_struct_0 @ X27)
% 0.21/0.50          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.21/0.50          | (v6_waybel_0 @ (k4_waybel_9 @ X27 @ X26 @ X28) @ X27))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k4_waybel_9])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v6_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (l1_struct_0 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.50  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((v6_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)),
% 0.21/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf(d7_waybel_9, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( l1_struct_0 @ A ) & ( ~( v2_struct_0 @ A ) ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( l1_waybel_0 @ B @ A ) & ( ~( v2_struct_0 @ B ) ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( ( l1_waybel_0 @ D @ A ) & ( v6_waybel_0 @ D @ A ) ) =>
% 0.21/0.50                   ( ( ( D ) = ( k4_waybel_9 @ A @ B @ C ) ) <=>
% 0.21/0.50                     ( ( ( u1_waybel_0 @ A @ D ) =
% 0.21/0.50                         ( k2_partfun1 @
% 0.21/0.50                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.50                           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.21/0.50                       ( r2_relset_1 @
% 0.21/0.50                         ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.21/0.50                         ( u1_orders_2 @ D ) @ 
% 0.21/0.50                         ( k1_toler_1 @
% 0.21/0.50                           ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.21/0.50                       ( ![E:$i]:
% 0.21/0.50                         ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) ) <=>
% 0.21/0.50                           ( ?[F:$i]:
% 0.21/0.50                             ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.50                               ( ( F ) = ( E ) ) & ( r1_orders_2 @ B @ C @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_2, axiom,
% 0.21/0.50    (![F:$i,E:$i,C:$i,B:$i]:
% 0.21/0.50     ( ( zip_tseitin_0 @ F @ E @ C @ B ) <=>
% 0.21/0.50       ( ( r1_orders_2 @ B @ C @ F ) & ( ( F ) = ( E ) ) & 
% 0.21/0.50         ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_3, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( ( v6_waybel_0 @ D @ A ) & ( l1_waybel_0 @ D @ A ) ) =>
% 0.21/0.50                   ( ( ( D ) = ( k4_waybel_9 @ A @ B @ C ) ) <=>
% 0.21/0.50                     ( ( ![E:$i]:
% 0.21/0.50                         ( ( r2_hidden @ E @ ( u1_struct_0 @ D ) ) <=>
% 0.21/0.50                           ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B ) ) ) ) & 
% 0.21/0.50                       ( r2_relset_1 @
% 0.21/0.50                         ( u1_struct_0 @ D ) @ ( u1_struct_0 @ D ) @ 
% 0.21/0.50                         ( u1_orders_2 @ D ) @ 
% 0.21/0.50                         ( k1_toler_1 @
% 0.21/0.50                           ( u1_orders_2 @ B ) @ ( u1_struct_0 @ D ) ) ) & 
% 0.21/0.50                       ( ( u1_waybel_0 @ A @ D ) =
% 0.21/0.50                         ( k2_partfun1 @
% 0.21/0.50                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.50                           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X25 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X18)
% 0.21/0.50          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.50          | ~ (v6_waybel_0 @ X20 @ X19)
% 0.21/0.50          | ~ (l1_waybel_0 @ X20 @ X19)
% 0.21/0.50          | ((X20) != (k4_waybel_9 @ X19 @ X18 @ X21))
% 0.21/0.50          | (zip_tseitin_0 @ (sk_F_1 @ X25 @ X21 @ X18) @ X25 @ X21 @ X18)
% 0.21/0.50          | ~ (r2_hidden @ X25 @ (u1_struct_0 @ X20))
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.21/0.50          | ~ (l1_struct_0 @ X19)
% 0.21/0.50          | (v2_struct_0 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X21 : $i, X25 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X19)
% 0.21/0.50          | ~ (l1_struct_0 @ X19)
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X18))
% 0.21/0.50          | ~ (r2_hidden @ X25 @ 
% 0.21/0.50               (u1_struct_0 @ (k4_waybel_9 @ X19 @ X18 @ X21)))
% 0.21/0.50          | (zip_tseitin_0 @ (sk_F_1 @ X25 @ X21 @ X18) @ X25 @ X21 @ X18)
% 0.21/0.50          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X19 @ X18 @ X21) @ X19)
% 0.21/0.50          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X19 @ X18 @ X21) @ X19)
% 0.21/0.50          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.50          | (v2_struct_0 @ X18))),
% 0.21/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ X2 @ X1 @ X0)) @ X3)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | ~ (l1_waybel_0 @ X1 @ X2)
% 0.21/0.50          | ~ (v6_waybel_0 @ (k4_waybel_9 @ X2 @ X1 @ X0) @ X2)
% 0.21/0.50          | ~ (l1_waybel_0 @ (k4_waybel_9 @ X2 @ X1 @ X0) @ X2)
% 0.21/0.50          | (zip_tseitin_0 @ 
% 0.21/0.50             (sk_F_1 @ 
% 0.21/0.50              (sk_C @ X3 @ (u1_struct_0 @ (k4_waybel_9 @ X2 @ X1 @ X0))) @ 
% 0.21/0.50              X0 @ X1) @ 
% 0.21/0.50             (sk_C @ X3 @ (u1_struct_0 @ (k4_waybel_9 @ X2 @ X1 @ X0))) @ X0 @ 
% 0.21/0.50             X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.50          | ~ (l1_struct_0 @ X2)
% 0.21/0.50          | (v2_struct_0 @ X2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | (zip_tseitin_0 @ 
% 0.21/0.50             (sk_F_1 @ 
% 0.21/0.50              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50              sk_C_1 @ sk_B) @ 
% 0.21/0.50             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50             sk_C_1 @ sk_B)
% 0.21/0.50          | ~ (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ 
% 0.21/0.50             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '22'])).
% 0.21/0.50  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.50         (~ (l1_waybel_0 @ X26 @ X27)
% 0.21/0.50          | (v2_struct_0 @ X26)
% 0.21/0.50          | ~ (l1_struct_0 @ X27)
% 0.21/0.50          | (v2_struct_0 @ X27)
% 0.21/0.50          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.21/0.50          | (l1_waybel_0 @ (k4_waybel_9 @ X27 @ X26 @ X28) @ X27))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k4_waybel_9])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((l1_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X0)
% 0.21/0.50          | (v2_struct_0 @ X0)
% 0.21/0.50          | ~ (l1_struct_0 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.50  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ sk_A)),
% 0.21/0.50      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (zip_tseitin_0 @ 
% 0.21/0.50             (sk_F_1 @ 
% 0.21/0.50              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50              sk_C_1 @ sk_B) @ 
% 0.21/0.50             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50             sk_C_1 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ 
% 0.21/0.50             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24', '25', '36', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (((X15) = (X16)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X14 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.21/0.50           X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | ((sk_F_1 @ 
% 0.21/0.50              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50              sk_C_1 @ sk_B)
% 0.21/0.50              = (sk_C @ X0 @ 
% 0.21/0.50                 (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (zip_tseitin_0 @ 
% 0.21/0.50             (sk_F_1 @ 
% 0.21/0.50              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50              sk_C_1 @ sk_B) @ 
% 0.21/0.50             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50             sk_C_1 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ 
% 0.21/0.50             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '24', '25', '36', '37'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         ((m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.21/0.50          | ~ (zip_tseitin_0 @ X15 @ X16 @ X14 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.21/0.50           X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (sk_F_1 @ 
% 0.21/0.50              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50              sk_C_1 @ sk_B) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf(t2_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]:
% 0.21/0.50         ((r2_hidden @ X4 @ X5)
% 0.21/0.50          | (v1_xboole_0 @ X5)
% 0.21/0.50          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ 
% 0.21/0.50             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (sk_F_1 @ 
% 0.21/0.50              (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50              sk_C_1 @ sk_B) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ 
% 0.21/0.50           (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50           (u1_struct_0 @ sk_B))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ 
% 0.21/0.50             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | (r1_tarski @ 
% 0.21/0.50             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['40', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | (r1_tarski @ 
% 0.21/0.50             (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (sk_C @ X0 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i]:
% 0.21/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.21/0.50           (u1_struct_0 @ sk_B))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.50        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.21/0.50           (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.50        | (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.21/0.50           (u1_struct_0 @ sk_B))
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (~ (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.21/0.50          (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)) | (v2_struct_0 @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('clc', [status(thm)], ['54', '55'])).
% 0.21/0.50  thf('57', plain, ((v1_xboole_0 @ (u1_waybel_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '56'])).
% 0.21/0.50  thf(fc15_yellow_6, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.21/0.50         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.21/0.50         ( ~( v1_xboole_0 @ ( u1_waybel_0 @ A @ B ) ) ) & 
% 0.21/0.50         ( v1_funct_2 @
% 0.21/0.50           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X11)
% 0.21/0.50          | (v2_struct_0 @ X11)
% 0.21/0.50          | (v2_struct_0 @ X12)
% 0.21/0.50          | ~ (l1_waybel_0 @ X12 @ X11)
% 0.21/0.50          | ~ (v1_xboole_0 @ (u1_waybel_0 @ X11 @ X12)))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc15_yellow_6])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      ((~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_B)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.50  thf('60', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('62', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.21/0.50  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('64', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.50  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
