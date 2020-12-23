%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1636+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CFZ6HrDSE8

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:53 EST 2020

% Result     : Theorem 10.89s
% Output     : Refutation 10.89s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 248 expanded)
%              Number of leaves         :   39 (  87 expanded)
%              Depth                    :   23
%              Number of atoms          : 1317 (2906 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(k4_waybel_0_type,type,(
    k4_waybel_0: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k3_waybel_0_type,type,(
    k3_waybel_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t16_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r1_tarski @ B @ ( k3_waybel_0 @ A @ B ) )
            & ( r1_tarski @ B @ ( k4_waybel_0 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r1_tarski @ B @ ( k3_waybel_0 @ A @ B ) )
              & ( r1_tarski @ B @ ( k4_waybel_0 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_waybel_0])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X30 @ X32 )
      | ( r2_hidden @ ( sk_C_1 @ X32 @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X30 @ X32 )
      | ( r2_hidden @ ( sk_C_1 @ X32 @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X31 )
      | ~ ( r1_tarski @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( l1_orders_2 @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d4_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_orders_2 @ A )
      <=> ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X33: $i] :
      ( ~ ( v3_orders_2 @ X33 )
      | ( r1_relat_2 @ ( u1_orders_2 @ X33 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_orders_2 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_orders_2])).

thf(d1_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_relat_2 @ A @ B )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
             => ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_relat_2 @ X26 @ X27 )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X28 ) @ X26 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( v3_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) ) @ ( u1_orders_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ ( u1_orders_2 @ X35 ) )
      | ( r1_orders_2 @ X35 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_orders_2 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X30 @ X32 )
      | ( r2_hidden @ ( sk_C_1 @ X32 @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('29',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( m1_subset_1 @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(d15_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k3_waybel_0 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ? [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                          & ( r1_orders_2 @ A @ D @ E )
                          & ( r2_hidden @ E @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r2_hidden @ E @ B )
        & ( r1_orders_2 @ A @ D @ E )
        & ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i,X7: $i] :
      ( ( zip_tseitin_0 @ X3 @ X5 @ X4 @ X7 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r1_orders_2 @ X7 @ X5 @ X3 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X2 @ ( sk_C_1 @ X0 @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X0 @ sk_B ) @ X2 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) @ X1 @ sk_A )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X1 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) @ X1 @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_0 @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) @ sk_B @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k3_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_orders_2 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( m1_subset_1 @ ( k3_waybel_0 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_0])).

thf('42',plain,
    ( ( m1_subset_1 @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k3_waybel_0 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ? [E: $i] :
                          ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( X10
       != ( k3_waybel_0 @ X9 @ X8 ) )
      | ( r2_hidden @ X11 @ X10 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X8: $i,X9: $i,X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ ( k3_waybel_0 @ X9 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X8 @ X9 )
      | ( r2_hidden @ X11 @ ( k3_waybel_0 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k3_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X30 @ X32 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X32 @ X30 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,
    ( ( r1_tarski @ sk_B @ ( k3_waybel_0 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ sk_B @ ( k3_waybel_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_waybel_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    r1_tarski @ sk_B @ ( k3_waybel_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,(
    ~ ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','60'])).

thf('62',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X30 @ X32 )
      | ( r2_hidden @ ( sk_C_1 @ X32 @ X30 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['26','31'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(d16_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k4_waybel_0 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ? [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                          & ( r1_orders_2 @ A @ E @ D )
                          & ( r2_hidden @ E @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ E @ D @ B @ A )
    <=> ( ( r2_hidden @ E @ B )
        & ( r1_orders_2 @ A @ E @ D )
        & ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_1 @ X14 @ X16 @ X15 @ X18 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_orders_2 @ X18 @ X14 @ X16 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C_1 @ X0 @ sk_B ) @ X2 )
      | ( zip_tseitin_1 @ ( sk_C_1 @ X0 @ sk_B ) @ X2 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) @ X1 @ sk_A )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X1 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X1 )
      | ( zip_tseitin_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) @ X1 @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( sk_C_1 @ X0 @ sk_B ) @ sk_B @ sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k4_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('72',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_orders_2 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_subset_1 @ ( k4_waybel_0 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_0])).

thf('73',plain,
    ( ( m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k4_waybel_0 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ? [E: $i] :
                          ( zip_tseitin_1 @ E @ D @ B @ A ) ) ) ) ) ) ) )).

thf('76',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( X21
       != ( k4_waybel_0 @ X20 @ X19 ) )
      | ( r2_hidden @ X22 @ X21 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('77',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( m1_subset_1 @ ( k4_waybel_0 @ X20 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X19 @ X20 )
      | ( r2_hidden @ X22 @ ( k4_waybel_0 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_1 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_1 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ X30 @ X32 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X32 @ X30 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('86',plain,
    ( ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['61','87'])).


%------------------------------------------------------------------------------
