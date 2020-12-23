%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1635+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6IsjkIO9lG

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:53 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  147 (1230 expanded)
%              Number of leaves         :   25 ( 348 expanded)
%              Depth                    :   31
%              Number of atoms          : 2047 (18315 expanded)
%              Number of equality atoms :   46 ( 658 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i )).

thf(a_2_1_waybel_0_type,type,(
    a_2_1_waybel_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_waybel_0_type,type,(
    k4_waybel_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t15_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_waybel_0 @ A @ B )
            = ( a_2_1_waybel_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k4_waybel_0 @ A @ B )
              = ( a_2_1_waybel_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_waybel_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k4_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( k4_waybel_0 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_0])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r2_hidden @ E @ B )
        & ( r1_orders_2 @ A @ E @ D )
        & ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
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
                          ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k4_waybel_0 @ X6 @ X5 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X8 @ X5 @ X6 ) @ X8 @ X5 @ X6 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( m1_subset_1 @ ( k4_waybel_0 @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_hidden @ X8 @ ( k4_waybel_0 @ X6 @ X5 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X8 @ X5 @ X6 ) @ X8 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ X0 )
      | ( X0
        = ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B @ sk_A ) @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ X0 )
      | ( X0
        = ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B @ sk_A ) @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ X0 )
      | ( X0
        = ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B @ sk_A ) @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_orders_2 @ X3 @ X0 @ X2 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) @ sk_B @ sk_A ) @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_2_1_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_1_waybel_0 @ B @ C ) )
      <=> ? [D: $i] :
            ( ? [E: $i] :
                ( ( r2_hidden @ E @ C )
                & ( r1_orders_2 @ B @ E @ D )
                & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( X15
        = ( sk_D_1 @ X14 @ X13 @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_waybel_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_waybel_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D_1 @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D_1 @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ sk_B @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ X0 )
      | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
        = X0 )
      | ( ( sk_C @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
        = ( sk_D_1 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X14 @ X13 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_waybel_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_waybel_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ X0 )
      | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
        = X0 )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A @ ( sk_C @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ X0 )
      | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ X0 )
      | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
        = X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
      = ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
      = ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ( k4_waybel_0 @ sk_A @ sk_B )
 != ( a_2_1_waybel_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r2_hidden @ X15 @ ( a_2_1_waybel_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ( X15 != X16 )
      | ~ ( r2_hidden @ X17 @ X14 )
      | ~ ( r1_orders_2 @ X13 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_waybel_0])).

thf('52',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ X17 @ X16 )
      | ~ ( r2_hidden @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ( r2_hidden @ X16 @ ( a_2_1_waybel_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,
    ( ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
    | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
      = ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','56'])).

thf('58',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
      = ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ( k4_waybel_0 @ sk_A @ sk_B )
 != ( a_2_1_waybel_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
    | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
      = ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
      = ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ( k4_waybel_0 @ sk_A @ sk_B )
 != ( a_2_1_waybel_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
    | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
      = ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','66'])).

thf('68',plain,
    ( ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
      = ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ( k4_waybel_0 @ sk_A @ sk_B )
 != ( a_2_1_waybel_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r2_hidden @ ( sk_E_2 @ X14 @ X13 @ X15 ) @ X14 )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_waybel_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_waybel_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_E_2 @ sk_B @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_E_2 @ sk_B @ sk_A @ X0 ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E_2 @ sk_B @ sk_A @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    r2_hidden @ ( sk_E_2 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_orders_2 @ X13 @ ( sk_E_2 @ X14 @ X13 @ X15 ) @ ( sk_D_1 @ X14 @ X13 @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_waybel_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_waybel_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E_2 @ sk_B @ sk_A @ X0 ) @ ( sk_D_1 @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_orders_2 @ sk_A @ ( sk_E_2 @ sk_B @ sk_A @ X0 ) @ ( sk_D_1 @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_E_2 @ sk_B @ sk_A @ X0 ) @ ( sk_D_1 @ sk_B @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    r1_orders_2 @ sk_A @ ( sk_E_2 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ ( sk_D_1 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,(
    r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ sk_B @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('90',plain,
    ( ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
    = ( sk_D_1 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    r1_orders_2 @ sk_A @ ( sk_E_2 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( sk_E_2 @ X14 @ X13 @ X15 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_waybel_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_waybel_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E_2 @ sk_B @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_E_2 @ sk_B @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_E_2 @ sk_B @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ ( sk_E_2 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_E_2 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_E_2 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_E_2 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_2 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ X0 @ sk_A )
      | ~ ( r2_hidden @ ( sk_E_2 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','102'])).

thf('104',plain,(
    zip_tseitin_0 @ ( sk_E_2 @ sk_B @ sk_A @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) ) @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['78','103'])).

thf('105',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('106',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k4_waybel_0 @ X6 @ X5 ) )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('107',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( m1_subset_1 @ ( k4_waybel_0 @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X5 @ X6 )
      | ( r2_hidden @ X8 @ ( k4_waybel_0 @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','111'])).

thf('113',plain,(
    m1_subset_1 @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('114',plain,(
    r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( k4_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ~ ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ~ ( r2_hidden @ ( sk_C @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('116',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) )
    | ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
      = ( k4_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    r2_hidden @ ( sk_C @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ) @ ( a_2_1_waybel_0 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('118',plain,
    ( ( a_2_1_waybel_0 @ sk_A @ sk_B )
    = ( k4_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ( k4_waybel_0 @ sk_A @ sk_B )
 != ( a_2_1_waybel_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).


%------------------------------------------------------------------------------
