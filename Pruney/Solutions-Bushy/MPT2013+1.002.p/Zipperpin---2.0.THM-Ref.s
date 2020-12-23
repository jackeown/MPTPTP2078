%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2013+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EhFZVku9Oz

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:40 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  151 (1095 expanded)
%              Number of leaves         :   30 ( 308 expanded)
%              Depth                    :   33
%              Number of atoms          : 2329 (20934 expanded)
%              Number of equality atoms :   55 ( 712 expanded)
%              Maximal formula depth    :   20 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(a_3_0_waybel_9_type,type,(
    a_3_0_waybel_9: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_toler_1_type,type,(
    k1_toler_1: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_waybel_9_type,type,(
    k4_waybel_9: $i > $i > $i > $i )).

thf(t12_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) )
                = ( a_3_0_waybel_9 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) )
                  = ( a_3_0_waybel_9 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_waybel_9])).

thf('0',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 = X21 )
      | ( r2_hidden @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ( r2_hidden @ ( sk_C @ X21 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_3_0_waybel_9,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l1_struct_0 @ B )
        & ~ ( v2_struct_0 @ C )
        & ( l1_waybel_0 @ C @ B )
        & ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) )
     => ( ( r2_hidden @ A @ ( a_3_0_waybel_9 @ B @ C @ D ) )
      <=> ? [E: $i] :
            ( ( r1_orders_2 @ C @ D @ E )
            & ( A = E )
            & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ( X19
        = ( sk_E_1 @ X18 @ X16 @ X19 ) )
      | ~ ( r2_hidden @ X19 @ ( a_3_0_waybel_9 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ( X1
        = ( sk_E_1 @ sk_C_1 @ sk_B @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 ) @ X1 )
      | ( X1
        = ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_C @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 )
        = ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
        = ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
        = ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 = X21 )
      | ( r2_hidden @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ( r2_hidden @ ( sk_C @ X21 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ( r1_orders_2 @ X16 @ X18 @ ( sk_E_1 @ X18 @ X16 @ X19 ) )
      | ~ ( r2_hidden @ X19 @ ( a_3_0_waybel_9 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 ) @ X1 )
      | ( X1
        = ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
        = ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 = X21 )
      | ( r2_hidden @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ( r2_hidden @ ( sk_C @ X21 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X18 @ X16 @ X19 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( r2_hidden @ X19 @ ( a_3_0_waybel_9 @ X17 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ X2 @ X1 @ X0 ) @ X3 ) @ X3 )
      | ( X3
        = ( a_3_0_waybel_9 @ X2 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_E_1 @ X0 @ X1 @ ( sk_C @ ( a_3_0_waybel_9 @ X2 @ X1 @ X0 ) @ X3 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( X1
        = ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_E_1 @ sk_C_1 @ sk_B @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

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

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B )
    <=> ( ( r1_orders_2 @ B @ C @ F )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) ) ) )).

thf('33',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X4 ) )
      | ( X2 != X3 )
      | ~ ( r1_orders_2 @ X4 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r1_orders_2 @ X4 @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ( zip_tseitin_0 @ X3 @ X3 @ X1 @ X4 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_B @ X1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ sk_C_1 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_waybel_0 @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( v6_waybel_0 @ ( k4_waybel_9 @ X14 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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

thf('50',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ X6 )
      | ~ ( v6_waybel_0 @ X7 @ X6 )
      | ~ ( l1_waybel_0 @ X7 @ X6 )
      | ( X7
       != ( k4_waybel_9 @ X6 @ X5 @ X8 ) )
      | ( r2_hidden @ X10 @ ( u1_struct_0 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X10 @ X8 @ X5 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X5 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X10 @ X8 @ X5 )
      | ( r2_hidden @ X10 @ ( u1_struct_0 @ ( k4_waybel_9 @ X6 @ X5 @ X8 ) ) )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X6 @ X5 @ X8 ) @ X6 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X6 @ X5 @ X8 ) @ X6 )
      | ~ ( l1_waybel_0 @ X5 @ X6 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) ) )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ sk_C_1 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_waybel_0 @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( l1_waybel_0 @ ( k4_waybel_9 @ X14 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( X0
        = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(eq_fact,[status(thm)],['69'])).

thf('71',plain,(
    ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
 != ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X12: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( l1_waybel_0 @ X5 @ X6 )
      | ~ ( v6_waybel_0 @ X7 @ X6 )
      | ~ ( l1_waybel_0 @ X7 @ X6 )
      | ( X7
       != ( k4_waybel_9 @ X6 @ X5 @ X8 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X8 @ X5 ) @ X12 @ X8 @ X5 )
      | ~ ( r2_hidden @ X12 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('78',plain,(
    ! [X5: $i,X6: $i,X8: $i,X12: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_hidden @ X12 @ ( u1_struct_0 @ ( k4_waybel_9 @ X6 @ X5 @ X8 ) ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X8 @ X5 ) @ X12 @ X8 @ X5 )
      | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ X6 @ X5 @ X8 ) @ X6 )
      | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ X6 @ X5 @ X8 ) @ X6 )
      | ~ ( l1_waybel_0 @ X5 @ X6 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
    | ~ ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v6_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['46','47'])).

thf('82',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(clc,[status(thm)],['63','64'])).

thf('83',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_orders_2 @ X0 @ X1 @ X2 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('91',plain,(
    r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_F_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ),
    inference(clc,[status(thm)],['87','88'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2 = X3 )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('94',plain,
    ( ( sk_F_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
    = ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    r1_orders_2 @ sk_B @ sk_C_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ),
    inference(clc,[status(thm)],['87','88'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X3 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('98',plain,(
    m1_subset_1 @ ( sk_F_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_F_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 @ sk_B )
    = ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('100',plain,(
    m1_subset_1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ X19 @ ( a_3_0_waybel_9 @ X17 @ X16 @ X18 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X16 ) )
      | ( X19 != X20 )
      | ~ ( r1_orders_2 @ X16 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('102',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ~ ( r1_orders_2 @ X16 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ X20 @ ( a_3_0_waybel_9 @ X17 @ X16 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_waybel_0 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ X0 @ sk_B @ X1 ) )
      | ~ ( r1_orders_2 @ sk_B @ X1 @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['100','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22 = X21 )
      | ~ ( r2_hidden @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ~ ( r2_hidden @ ( sk_C @ X21 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('115',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) )
    | ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    r2_hidden @ ( sk_C @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('117',plain,
    ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
 != ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['117','118'])).


%------------------------------------------------------------------------------
