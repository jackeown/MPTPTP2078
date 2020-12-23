%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HxNUJ6FUF6

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:56 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :  182 (2105 expanded)
%              Number of leaves         :   31 ( 603 expanded)
%              Depth                    :   34
%              Number of atoms          : 1917 (40227 expanded)
%              Number of equality atoms :   43 ( 307 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('1',plain,(
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
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X14: $i,X15: $i,X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r2_hidden @ X17 @ ( a_2_0_orders_2 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X14 ) )
      | ( X17 != X18 )
      | ( r2_hidden @ ( sk_E @ X18 @ X15 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('10',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_E @ X18 @ X15 @ X14 ) @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ X18 @ ( a_2_0_orders_2 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v2_struct_0 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
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
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

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

thf('17',plain,(
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

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
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
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('34',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ( r2_hidden @ ( sk_E @ X18 @ X15 @ X14 ) @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ X18 @ ( a_2_0_orders_2 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v2_struct_0 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('38',plain,(
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
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('45',plain,(
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

thf('46',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('47',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('52',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('53',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['54'])).

thf('58',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('61',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('62',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('63',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X17
        = ( sk_D_1 @ X15 @ X14 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_orders_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

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

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_C
      = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,
    ( ( ( sk_C
        = ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','73'])).

thf('75',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('77',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','77'])).

thf('79',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('80',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('81',plain,
    ( ( ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('83',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( r2_orders_2 @ X14 @ X16 @ ( sk_D_1 @ X15 @ X14 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_orders_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('84',plain,(
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
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['81','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['78','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','96'])).

thf('98',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['54'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(dt_k1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('102',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_orders_2 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_orders_2])).

thf('103',plain,
    ( ( m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['100','112'])).

thf('114',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','113'])).

thf('115',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['57','114'])).

thf('116',plain,
    ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['56','115'])).

thf('117',plain,
    ( ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','116'])).

thf('118',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('122',plain,(
    ! [X14: $i,X15: $i,X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r2_hidden @ X17 @ ( a_2_0_orders_2 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X14 ) )
      | ( X17 != X18 )
      | ~ ( r2_orders_2 @ X14 @ ( sk_E @ X18 @ X15 @ X14 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('123',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( r2_orders_2 @ X14 @ ( sk_E @ X18 @ X15 @ X14 ) @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X14 ) )
      | ( r2_hidden @ X18 @ ( a_2_0_orders_2 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v2_struct_0 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
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
    inference('sup-',[status(thm)],['121','123'])).

thf('125',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['124','125','126','127','128'])).

thf('130',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','129'])).

thf('131',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['58'])).

thf('132',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['58'])).

thf('133',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['57','114','132'])).

thf('134',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['131','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','134','135'])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['56','115'])).

thf('141',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','141'])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['27','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('147',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('148',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    $false ),
    inference('sup-',[status(thm)],['145','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HxNUJ6FUF6
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:43:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.10/1.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.10/1.31  % Solved by: fo/fo7.sh
% 1.10/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.10/1.31  % done 1710 iterations in 0.850s
% 1.10/1.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.10/1.31  % SZS output start Refutation
% 1.10/1.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.10/1.31  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.10/1.31  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.10/1.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.10/1.31  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.10/1.31  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 1.10/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.10/1.31  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.10/1.31  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 1.10/1.31  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.10/1.31  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 1.10/1.31  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 1.10/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.10/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.10/1.31  thf(sk_C_type, type, sk_C: $i).
% 1.10/1.31  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.10/1.31  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.10/1.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.10/1.31  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.10/1.31  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 1.10/1.31  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.10/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.10/1.31  thf(t51_orders_2, conjecture,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.10/1.31         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.10/1.31           ( ![C:$i]:
% 1.10/1.31             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.10/1.31               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 1.10/1.31                 ( r2_hidden @
% 1.10/1.31                   C @ 
% 1.10/1.31                   ( k1_orders_2 @
% 1.10/1.31                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ))).
% 1.10/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.10/1.31    (~( ![A:$i]:
% 1.10/1.31        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.10/1.31            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.10/1.31          ( ![B:$i]:
% 1.10/1.31            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.10/1.31              ( ![C:$i]:
% 1.10/1.31                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.10/1.31                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 1.10/1.31                    ( r2_hidden @
% 1.10/1.31                      C @ 
% 1.10/1.31                      ( k1_orders_2 @
% 1.10/1.31                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ) )),
% 1.10/1.31    inference('cnf.neg', [status(esa)], [t51_orders_2])).
% 1.10/1.31  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(t35_orders_2, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.10/1.31           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 1.10/1.31             ( m1_subset_1 @
% 1.10/1.31               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.10/1.31               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.10/1.31  thf('2', plain,
% 1.10/1.31      (![X21 : $i, X22 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 1.10/1.31          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21) @ 
% 1.10/1.31             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.10/1.31          | ~ (l1_orders_2 @ X22)
% 1.10/1.31          | ~ (v3_orders_2 @ X22)
% 1.10/1.31          | (v2_struct_0 @ X22))),
% 1.10/1.31      inference('cnf', [status(esa)], [t35_orders_2])).
% 1.10/1.31  thf('3', plain,
% 1.10/1.31      (((v2_struct_0 @ sk_A)
% 1.10/1.31        | ~ (v3_orders_2 @ sk_A)
% 1.10/1.31        | ~ (l1_orders_2 @ sk_A)
% 1.10/1.31        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.10/1.31           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['1', '2'])).
% 1.10/1.31  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('6', plain,
% 1.10/1.31      (((v2_struct_0 @ sk_A)
% 1.10/1.31        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.10/1.31           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.10/1.31      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.10/1.31  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('8', plain,
% 1.10/1.31      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.10/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('clc', [status(thm)], ['6', '7'])).
% 1.10/1.31  thf(fraenkel_a_2_0_orders_2, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 1.10/1.31         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 1.10/1.31         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 1.10/1.31       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 1.10/1.31         ( ?[D:$i]:
% 1.10/1.31           ( ( ![E:$i]:
% 1.10/1.31               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.10/1.31                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 1.10/1.31             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.10/1.31  thf('9', plain,
% 1.10/1.31      (![X14 : $i, X15 : $i, X17 : $i, X18 : $i]:
% 1.10/1.31         (~ (l1_orders_2 @ X14)
% 1.10/1.31          | ~ (v5_orders_2 @ X14)
% 1.10/1.31          | ~ (v4_orders_2 @ X14)
% 1.10/1.31          | ~ (v3_orders_2 @ X14)
% 1.10/1.31          | (v2_struct_0 @ X14)
% 1.10/1.31          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.10/1.31          | (r2_hidden @ X17 @ (a_2_0_orders_2 @ X14 @ X15))
% 1.10/1.31          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X14))
% 1.10/1.31          | ((X17) != (X18))
% 1.10/1.31          | (r2_hidden @ (sk_E @ X18 @ X15 @ X14) @ X15))),
% 1.10/1.31      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 1.10/1.31  thf('10', plain,
% 1.10/1.31      (![X14 : $i, X15 : $i, X18 : $i]:
% 1.10/1.31         ((r2_hidden @ (sk_E @ X18 @ X15 @ X14) @ X15)
% 1.10/1.31          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X14))
% 1.10/1.31          | (r2_hidden @ X18 @ (a_2_0_orders_2 @ X14 @ X15))
% 1.10/1.31          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.10/1.31          | (v2_struct_0 @ X14)
% 1.10/1.31          | ~ (v3_orders_2 @ X14)
% 1.10/1.31          | ~ (v4_orders_2 @ X14)
% 1.10/1.31          | ~ (v5_orders_2 @ X14)
% 1.10/1.31          | ~ (l1_orders_2 @ X14))),
% 1.10/1.31      inference('simplify', [status(thm)], ['9'])).
% 1.10/1.31  thf('11', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         (~ (l1_orders_2 @ sk_A)
% 1.10/1.31          | ~ (v5_orders_2 @ sk_A)
% 1.10/1.31          | ~ (v4_orders_2 @ sk_A)
% 1.10/1.31          | ~ (v3_orders_2 @ sk_A)
% 1.10/1.31          | (v2_struct_0 @ sk_A)
% 1.10/1.31          | (r2_hidden @ X0 @ 
% 1.10/1.31             (a_2_0_orders_2 @ sk_A @ 
% 1.10/1.31              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.10/1.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.10/1.31          | (r2_hidden @ 
% 1.10/1.31             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 1.10/1.31             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['8', '10'])).
% 1.10/1.31  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('13', plain, ((v5_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('16', plain,
% 1.10/1.31      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.10/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('clc', [status(thm)], ['6', '7'])).
% 1.10/1.31  thf(d12_orders_2, axiom,
% 1.10/1.31    (![A:$i]:
% 1.10/1.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.10/1.31         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.10/1.31       ( ![B:$i]:
% 1.10/1.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.10/1.31           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 1.10/1.31  thf('17', plain,
% 1.10/1.31      (![X10 : $i, X11 : $i]:
% 1.10/1.31         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.10/1.31          | ((k1_orders_2 @ X11 @ X10) = (a_2_0_orders_2 @ X11 @ X10))
% 1.10/1.31          | ~ (l1_orders_2 @ X11)
% 1.10/1.31          | ~ (v5_orders_2 @ X11)
% 1.10/1.31          | ~ (v4_orders_2 @ X11)
% 1.10/1.31          | ~ (v3_orders_2 @ X11)
% 1.10/1.31          | (v2_struct_0 @ X11))),
% 1.10/1.31      inference('cnf', [status(esa)], [d12_orders_2])).
% 1.10/1.31  thf('18', plain,
% 1.10/1.31      (((v2_struct_0 @ sk_A)
% 1.10/1.31        | ~ (v3_orders_2 @ sk_A)
% 1.10/1.31        | ~ (v4_orders_2 @ sk_A)
% 1.10/1.31        | ~ (v5_orders_2 @ sk_A)
% 1.10/1.31        | ~ (l1_orders_2 @ sk_A)
% 1.10/1.31        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.10/1.31            = (a_2_0_orders_2 @ sk_A @ 
% 1.10/1.31               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.10/1.31      inference('sup-', [status(thm)], ['16', '17'])).
% 1.10/1.31  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('23', plain,
% 1.10/1.31      (((v2_struct_0 @ sk_A)
% 1.10/1.31        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.10/1.31            = (a_2_0_orders_2 @ sk_A @ 
% 1.10/1.31               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.10/1.31      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 1.10/1.31  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('25', plain,
% 1.10/1.31      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.10/1.31         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.10/1.31      inference('clc', [status(thm)], ['23', '24'])).
% 1.10/1.31  thf('26', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         ((v2_struct_0 @ sk_A)
% 1.10/1.31          | (r2_hidden @ X0 @ 
% 1.10/1.31             (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.10/1.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.10/1.31          | (r2_hidden @ 
% 1.10/1.31             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 1.10/1.31             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.10/1.31      inference('demod', [status(thm)], ['11', '12', '13', '14', '15', '25'])).
% 1.10/1.31  thf('27', plain,
% 1.10/1.31      (((r2_hidden @ 
% 1.10/1.31         (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 1.10/1.31         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.10/1.31        | (r2_hidden @ sk_B @ 
% 1.10/1.31           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.10/1.31        | (v2_struct_0 @ sk_A))),
% 1.10/1.31      inference('sup-', [status(thm)], ['0', '26'])).
% 1.10/1.31  thf('28', plain,
% 1.10/1.31      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.10/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('clc', [status(thm)], ['6', '7'])).
% 1.10/1.31  thf(t5_subset, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.10/1.31          ( v1_xboole_0 @ C ) ) ))).
% 1.10/1.31  thf('29', plain,
% 1.10/1.31      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.10/1.31         (~ (r2_hidden @ X7 @ X8)
% 1.10/1.31          | ~ (v1_xboole_0 @ X9)
% 1.10/1.31          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.10/1.31      inference('cnf', [status(esa)], [t5_subset])).
% 1.10/1.31  thf('30', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.31          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['28', '29'])).
% 1.10/1.31  thf('31', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf(redefinition_k6_domain_1, axiom,
% 1.10/1.31    (![A:$i,B:$i]:
% 1.10/1.31     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.10/1.31       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.10/1.31  thf('33', plain,
% 1.10/1.31      (![X19 : $i, X20 : $i]:
% 1.10/1.31         ((v1_xboole_0 @ X19)
% 1.10/1.31          | ~ (m1_subset_1 @ X20 @ X19)
% 1.10/1.31          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 1.10/1.31      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.10/1.31  thf('34', plain,
% 1.10/1.31      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 1.10/1.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['32', '33'])).
% 1.10/1.31  thf('35', plain,
% 1.10/1.31      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.10/1.31        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('clc', [status(thm)], ['6', '7'])).
% 1.10/1.31  thf('36', plain,
% 1.10/1.31      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 1.10/1.31         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.10/1.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('sup+', [status(thm)], ['34', '35'])).
% 1.10/1.31  thf('37', plain,
% 1.10/1.31      (![X14 : $i, X15 : $i, X18 : $i]:
% 1.10/1.31         ((r2_hidden @ (sk_E @ X18 @ X15 @ X14) @ X15)
% 1.10/1.31          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X14))
% 1.10/1.31          | (r2_hidden @ X18 @ (a_2_0_orders_2 @ X14 @ X15))
% 1.10/1.31          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.10/1.31          | (v2_struct_0 @ X14)
% 1.10/1.31          | ~ (v3_orders_2 @ X14)
% 1.10/1.31          | ~ (v4_orders_2 @ X14)
% 1.10/1.31          | ~ (v5_orders_2 @ X14)
% 1.10/1.31          | ~ (l1_orders_2 @ X14))),
% 1.10/1.31      inference('simplify', [status(thm)], ['9'])).
% 1.10/1.31  thf('38', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.31          | ~ (l1_orders_2 @ sk_A)
% 1.10/1.31          | ~ (v5_orders_2 @ sk_A)
% 1.10/1.31          | ~ (v4_orders_2 @ sk_A)
% 1.10/1.31          | ~ (v3_orders_2 @ sk_A)
% 1.10/1.31          | (v2_struct_0 @ sk_A)
% 1.10/1.31          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.10/1.31          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 1.10/1.31             (k1_tarski @ sk_B)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['36', '37'])).
% 1.10/1.31  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('40', plain, ((v5_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('41', plain, ((v4_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('42', plain, ((v3_orders_2 @ sk_A)),
% 1.10/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.31  thf('43', plain,
% 1.10/1.31      (![X0 : $i]:
% 1.10/1.31         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.31          | (v2_struct_0 @ sk_A)
% 1.10/1.31          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.10/1.31          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 1.10/1.31             (k1_tarski @ sk_B)))),
% 1.10/1.31      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 1.10/1.31  thf('44', plain,
% 1.10/1.31      (((r2_hidden @ (sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 1.10/1.31         (k1_tarski @ sk_B))
% 1.10/1.31        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.31        | (v2_struct_0 @ sk_A)
% 1.10/1.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['31', '43'])).
% 1.10/1.31  thf(t69_enumset1, axiom,
% 1.10/1.31    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.10/1.31  thf('45', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.10/1.31      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.10/1.31  thf(d2_tarski, axiom,
% 1.10/1.31    (![A:$i,B:$i,C:$i]:
% 1.10/1.31     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.10/1.31       ( ![D:$i]:
% 1.10/1.31         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.10/1.31  thf('46', plain,
% 1.10/1.31      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.10/1.31         (~ (r2_hidden @ X4 @ X2)
% 1.10/1.31          | ((X4) = (X3))
% 1.10/1.31          | ((X4) = (X0))
% 1.10/1.31          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 1.10/1.31      inference('cnf', [status(esa)], [d2_tarski])).
% 1.10/1.31  thf('47', plain,
% 1.10/1.31      (![X0 : $i, X3 : $i, X4 : $i]:
% 1.10/1.31         (((X4) = (X0))
% 1.10/1.31          | ((X4) = (X3))
% 1.10/1.31          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 1.10/1.31      inference('simplify', [status(thm)], ['46'])).
% 1.10/1.31  thf('48', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['45', '47'])).
% 1.10/1.31  thf('49', plain,
% 1.10/1.31      (![X0 : $i, X1 : $i]:
% 1.10/1.31         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.10/1.31      inference('simplify', [status(thm)], ['48'])).
% 1.10/1.31  thf('50', plain,
% 1.10/1.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.31        | (v2_struct_0 @ sk_A)
% 1.10/1.31        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.31        | ((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['44', '49'])).
% 1.10/1.31  thf('51', plain,
% 1.10/1.31      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 1.10/1.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.31      inference('sup-', [status(thm)], ['32', '33'])).
% 1.10/1.31  thf('52', plain,
% 1.10/1.31      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.10/1.31         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.10/1.31      inference('clc', [status(thm)], ['23', '24'])).
% 1.10/1.31  thf('53', plain,
% 1.10/1.31      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.10/1.31          = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('sup+', [status(thm)], ['51', '52'])).
% 1.10/1.32  thf('54', plain,
% 1.10/1.32      ((~ (r2_hidden @ sk_C @ 
% 1.10/1.32           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.10/1.32        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('55', plain,
% 1.10/1.32      ((~ (r2_hidden @ sk_C @ 
% 1.10/1.32           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 1.10/1.32         <= (~
% 1.10/1.32             ((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('split', [status(esa)], ['54'])).
% 1.10/1.32  thf('56', plain,
% 1.10/1.32      (((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.10/1.32         <= (~
% 1.10/1.32             ((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('sup-', [status(thm)], ['53', '55'])).
% 1.10/1.32  thf('57', plain,
% 1.10/1.32      (~
% 1.10/1.32       ((r2_hidden @ sk_C @ 
% 1.10/1.32         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))) | 
% 1.10/1.32       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.10/1.32      inference('split', [status(esa)], ['54'])).
% 1.10/1.32  thf('58', plain,
% 1.10/1.32      (((r2_hidden @ sk_C @ 
% 1.10/1.32         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.10/1.32        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('59', plain,
% 1.10/1.32      (((r2_hidden @ sk_C @ 
% 1.10/1.32         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('split', [status(esa)], ['58'])).
% 1.10/1.32  thf('60', plain,
% 1.10/1.32      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('sup-', [status(thm)], ['32', '33'])).
% 1.10/1.32  thf('61', plain,
% 1.10/1.32      (((r2_hidden @ sk_C @ 
% 1.10/1.32         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('split', [status(esa)], ['58'])).
% 1.10/1.32  thf('62', plain,
% 1.10/1.32      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.10/1.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('clc', [status(thm)], ['6', '7'])).
% 1.10/1.32  thf('63', plain,
% 1.10/1.32      (![X14 : $i, X15 : $i, X17 : $i]:
% 1.10/1.32         (~ (l1_orders_2 @ X14)
% 1.10/1.32          | ~ (v5_orders_2 @ X14)
% 1.10/1.32          | ~ (v4_orders_2 @ X14)
% 1.10/1.32          | ~ (v3_orders_2 @ X14)
% 1.10/1.32          | (v2_struct_0 @ X14)
% 1.10/1.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.10/1.32          | ((X17) = (sk_D_1 @ X15 @ X14 @ X17))
% 1.10/1.32          | ~ (r2_hidden @ X17 @ (a_2_0_orders_2 @ X14 @ X15)))),
% 1.10/1.32      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 1.10/1.32  thf('64', plain,
% 1.10/1.32      (![X0 : $i]:
% 1.10/1.32         (~ (r2_hidden @ X0 @ 
% 1.10/1.32             (a_2_0_orders_2 @ sk_A @ 
% 1.10/1.32              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.10/1.32          | ((X0)
% 1.10/1.32              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ 
% 1.10/1.32                 X0))
% 1.10/1.32          | (v2_struct_0 @ sk_A)
% 1.10/1.32          | ~ (v3_orders_2 @ sk_A)
% 1.10/1.32          | ~ (v4_orders_2 @ sk_A)
% 1.10/1.32          | ~ (v5_orders_2 @ sk_A)
% 1.10/1.32          | ~ (l1_orders_2 @ sk_A))),
% 1.10/1.32      inference('sup-', [status(thm)], ['62', '63'])).
% 1.10/1.32  thf('65', plain,
% 1.10/1.32      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.10/1.32         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.10/1.32      inference('clc', [status(thm)], ['23', '24'])).
% 1.10/1.32  thf('66', plain, ((v3_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('67', plain, ((v4_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('68', plain, ((v5_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('70', plain,
% 1.10/1.32      (![X0 : $i]:
% 1.10/1.32         (~ (r2_hidden @ X0 @ 
% 1.10/1.32             (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.10/1.32          | ((X0)
% 1.10/1.32              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ 
% 1.10/1.32                 X0))
% 1.10/1.32          | (v2_struct_0 @ sk_A))),
% 1.10/1.32      inference('demod', [status(thm)], ['64', '65', '66', '67', '68', '69'])).
% 1.10/1.32  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('72', plain,
% 1.10/1.32      (![X0 : $i]:
% 1.10/1.32         (((X0)
% 1.10/1.32            = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ X0))
% 1.10/1.32          | ~ (r2_hidden @ X0 @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.10/1.32      inference('clc', [status(thm)], ['70', '71'])).
% 1.10/1.32  thf('73', plain,
% 1.10/1.32      ((((sk_C)
% 1.10/1.32          = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ sk_C)))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('sup-', [status(thm)], ['61', '72'])).
% 1.10/1.32  thf('74', plain,
% 1.10/1.32      (((((sk_C) = (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 1.10/1.32         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('sup+', [status(thm)], ['60', '73'])).
% 1.10/1.32  thf('75', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.10/1.32      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.10/1.32  thf('76', plain,
% 1.10/1.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.10/1.32         (((X1) != (X0))
% 1.10/1.32          | (r2_hidden @ X1 @ X2)
% 1.10/1.32          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 1.10/1.32      inference('cnf', [status(esa)], [d2_tarski])).
% 1.10/1.32  thf('77', plain,
% 1.10/1.32      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 1.10/1.32      inference('simplify', [status(thm)], ['76'])).
% 1.10/1.32  thf('78', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.10/1.32      inference('sup+', [status(thm)], ['75', '77'])).
% 1.10/1.32  thf('79', plain,
% 1.10/1.32      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.10/1.32          = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('sup+', [status(thm)], ['51', '52'])).
% 1.10/1.32  thf('80', plain,
% 1.10/1.32      (((r2_hidden @ sk_C @ 
% 1.10/1.32         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('split', [status(esa)], ['58'])).
% 1.10/1.32  thf('81', plain,
% 1.10/1.32      ((((r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('sup+', [status(thm)], ['79', '80'])).
% 1.10/1.32  thf('82', plain,
% 1.10/1.32      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 1.10/1.32         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('sup+', [status(thm)], ['34', '35'])).
% 1.10/1.32  thf('83', plain,
% 1.10/1.32      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.10/1.32         (~ (l1_orders_2 @ X14)
% 1.10/1.32          | ~ (v5_orders_2 @ X14)
% 1.10/1.32          | ~ (v4_orders_2 @ X14)
% 1.10/1.32          | ~ (v3_orders_2 @ X14)
% 1.10/1.32          | (v2_struct_0 @ X14)
% 1.10/1.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.10/1.32          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 1.10/1.32          | (r2_orders_2 @ X14 @ X16 @ (sk_D_1 @ X15 @ X14 @ X17))
% 1.10/1.32          | ~ (r2_hidden @ X16 @ X15)
% 1.10/1.32          | ~ (r2_hidden @ X17 @ (a_2_0_orders_2 @ X14 @ X15)))),
% 1.10/1.32      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 1.10/1.32  thf('84', plain,
% 1.10/1.32      (![X0 : $i, X1 : $i]:
% 1.10/1.32         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B))
% 1.10/1.32          | (r2_orders_2 @ sk_A @ X1 @ 
% 1.10/1.32             (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 1.10/1.32          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.10/1.32          | (v2_struct_0 @ sk_A)
% 1.10/1.32          | ~ (v3_orders_2 @ sk_A)
% 1.10/1.32          | ~ (v4_orders_2 @ sk_A)
% 1.10/1.32          | ~ (v5_orders_2 @ sk_A)
% 1.10/1.32          | ~ (l1_orders_2 @ sk_A))),
% 1.10/1.32      inference('sup-', [status(thm)], ['82', '83'])).
% 1.10/1.32  thf('85', plain, ((v3_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('86', plain, ((v4_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('87', plain, ((v5_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('88', plain, ((l1_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('89', plain,
% 1.10/1.32      (![X0 : $i, X1 : $i]:
% 1.10/1.32         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B))
% 1.10/1.32          | (r2_orders_2 @ sk_A @ X1 @ 
% 1.10/1.32             (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 1.10/1.32          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.10/1.32          | (v2_struct_0 @ sk_A))),
% 1.10/1.32      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 1.10/1.32  thf('90', plain,
% 1.10/1.32      ((![X0 : $i]:
% 1.10/1.32          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32           | (v2_struct_0 @ sk_A)
% 1.10/1.32           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32           | (r2_orders_2 @ sk_A @ X0 @ 
% 1.10/1.32              (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 1.10/1.32           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 1.10/1.32           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('sup-', [status(thm)], ['81', '89'])).
% 1.10/1.32  thf('91', plain,
% 1.10/1.32      ((![X0 : $i]:
% 1.10/1.32          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 1.10/1.32           | (r2_orders_2 @ sk_A @ X0 @ 
% 1.10/1.32              (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 1.10/1.32           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32           | (v2_struct_0 @ sk_A)
% 1.10/1.32           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('simplify', [status(thm)], ['90'])).
% 1.10/1.32  thf('92', plain,
% 1.10/1.32      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32         | (v2_struct_0 @ sk_A)
% 1.10/1.32         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.10/1.32         | (r2_orders_2 @ sk_A @ sk_B @ 
% 1.10/1.32            (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('sup-', [status(thm)], ['78', '91'])).
% 1.10/1.32  thf('93', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('94', plain,
% 1.10/1.32      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32         | (v2_struct_0 @ sk_A)
% 1.10/1.32         | (r2_orders_2 @ sk_A @ sk_B @ 
% 1.10/1.32            (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('demod', [status(thm)], ['92', '93'])).
% 1.10/1.32  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('96', plain,
% 1.10/1.32      ((((r2_orders_2 @ sk_A @ sk_B @ 
% 1.10/1.32          (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 1.10/1.32         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('clc', [status(thm)], ['94', '95'])).
% 1.10/1.32  thf('97', plain,
% 1.10/1.32      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 1.10/1.32         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('sup+', [status(thm)], ['74', '96'])).
% 1.10/1.32  thf('98', plain,
% 1.10/1.32      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 1.10/1.32         <= (((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('simplify', [status(thm)], ['97'])).
% 1.10/1.32  thf('99', plain,
% 1.10/1.32      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 1.10/1.32         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.10/1.32      inference('split', [status(esa)], ['54'])).
% 1.10/1.32  thf('100', plain,
% 1.10/1.32      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.10/1.32         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 1.10/1.32             ((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('sup-', [status(thm)], ['98', '99'])).
% 1.10/1.32  thf('101', plain,
% 1.10/1.32      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.10/1.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('clc', [status(thm)], ['6', '7'])).
% 1.10/1.32  thf(dt_k1_orders_2, axiom,
% 1.10/1.32    (![A:$i,B:$i]:
% 1.10/1.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.10/1.32         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 1.10/1.32         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.10/1.32       ( m1_subset_1 @
% 1.10/1.32         ( k1_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.10/1.32  thf('102', plain,
% 1.10/1.32      (![X12 : $i, X13 : $i]:
% 1.10/1.32         (~ (l1_orders_2 @ X12)
% 1.10/1.32          | ~ (v5_orders_2 @ X12)
% 1.10/1.32          | ~ (v4_orders_2 @ X12)
% 1.10/1.32          | ~ (v3_orders_2 @ X12)
% 1.10/1.32          | (v2_struct_0 @ X12)
% 1.10/1.32          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.10/1.32          | (m1_subset_1 @ (k1_orders_2 @ X12 @ X13) @ 
% 1.10/1.32             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 1.10/1.32      inference('cnf', [status(esa)], [dt_k1_orders_2])).
% 1.10/1.32  thf('103', plain,
% 1.10/1.32      (((m1_subset_1 @ 
% 1.10/1.32         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.10/1.32         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.10/1.32        | (v2_struct_0 @ sk_A)
% 1.10/1.32        | ~ (v3_orders_2 @ sk_A)
% 1.10/1.32        | ~ (v4_orders_2 @ sk_A)
% 1.10/1.32        | ~ (v5_orders_2 @ sk_A)
% 1.10/1.32        | ~ (l1_orders_2 @ sk_A))),
% 1.10/1.32      inference('sup-', [status(thm)], ['101', '102'])).
% 1.10/1.32  thf('104', plain, ((v3_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('105', plain, ((v4_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('106', plain, ((v5_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('108', plain,
% 1.10/1.32      (((m1_subset_1 @ 
% 1.10/1.32         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.10/1.32         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.10/1.32        | (v2_struct_0 @ sk_A))),
% 1.10/1.32      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 1.10/1.32  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('110', plain,
% 1.10/1.32      ((m1_subset_1 @ 
% 1.10/1.32        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.10/1.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('clc', [status(thm)], ['108', '109'])).
% 1.10/1.32  thf('111', plain,
% 1.10/1.32      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.10/1.32         (~ (r2_hidden @ X7 @ X8)
% 1.10/1.32          | ~ (v1_xboole_0 @ X9)
% 1.10/1.32          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.10/1.32      inference('cnf', [status(esa)], [t5_subset])).
% 1.10/1.32  thf('112', plain,
% 1.10/1.32      (![X0 : $i]:
% 1.10/1.32         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32          | ~ (r2_hidden @ X0 @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.10/1.32      inference('sup-', [status(thm)], ['110', '111'])).
% 1.10/1.32  thf('113', plain,
% 1.10/1.32      ((![X0 : $i]:
% 1.10/1.32          ~ (r2_hidden @ X0 @ 
% 1.10/1.32             (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 1.10/1.32         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 1.10/1.32             ((r2_hidden @ sk_C @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.10/1.32      inference('sup-', [status(thm)], ['100', '112'])).
% 1.10/1.32  thf('114', plain,
% 1.10/1.32      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 1.10/1.32       ~
% 1.10/1.32       ((r2_hidden @ sk_C @ 
% 1.10/1.32         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.10/1.32      inference('sup-', [status(thm)], ['59', '113'])).
% 1.10/1.32  thf('115', plain,
% 1.10/1.32      (~
% 1.10/1.32       ((r2_hidden @ sk_C @ 
% 1.10/1.32         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.10/1.32      inference('sat_resolution*', [status(thm)], ['57', '114'])).
% 1.10/1.32  thf('116', plain,
% 1.10/1.32      ((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('simpl_trail', [status(thm)], ['56', '115'])).
% 1.10/1.32  thf('117', plain,
% 1.10/1.32      ((((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B))
% 1.10/1.32        | (v2_struct_0 @ sk_A)
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('sup-', [status(thm)], ['50', '116'])).
% 1.10/1.32  thf('118', plain,
% 1.10/1.32      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32        | (v2_struct_0 @ sk_A)
% 1.10/1.32        | ((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B)))),
% 1.10/1.32      inference('simplify', [status(thm)], ['117'])).
% 1.10/1.32  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('120', plain,
% 1.10/1.32      ((((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B))
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('clc', [status(thm)], ['118', '119'])).
% 1.10/1.32  thf('121', plain,
% 1.10/1.32      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 1.10/1.32         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('sup+', [status(thm)], ['34', '35'])).
% 1.10/1.32  thf('122', plain,
% 1.10/1.32      (![X14 : $i, X15 : $i, X17 : $i, X18 : $i]:
% 1.10/1.32         (~ (l1_orders_2 @ X14)
% 1.10/1.32          | ~ (v5_orders_2 @ X14)
% 1.10/1.32          | ~ (v4_orders_2 @ X14)
% 1.10/1.32          | ~ (v3_orders_2 @ X14)
% 1.10/1.32          | (v2_struct_0 @ X14)
% 1.10/1.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.10/1.32          | (r2_hidden @ X17 @ (a_2_0_orders_2 @ X14 @ X15))
% 1.10/1.32          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X14))
% 1.10/1.32          | ((X17) != (X18))
% 1.10/1.32          | ~ (r2_orders_2 @ X14 @ (sk_E @ X18 @ X15 @ X14) @ X18))),
% 1.10/1.32      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 1.10/1.32  thf('123', plain,
% 1.10/1.32      (![X14 : $i, X15 : $i, X18 : $i]:
% 1.10/1.32         (~ (r2_orders_2 @ X14 @ (sk_E @ X18 @ X15 @ X14) @ X18)
% 1.10/1.32          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X14))
% 1.10/1.32          | (r2_hidden @ X18 @ (a_2_0_orders_2 @ X14 @ X15))
% 1.10/1.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.10/1.32          | (v2_struct_0 @ X14)
% 1.10/1.32          | ~ (v3_orders_2 @ X14)
% 1.10/1.32          | ~ (v4_orders_2 @ X14)
% 1.10/1.32          | ~ (v5_orders_2 @ X14)
% 1.10/1.32          | ~ (l1_orders_2 @ X14))),
% 1.10/1.32      inference('simplify', [status(thm)], ['122'])).
% 1.10/1.32  thf('124', plain,
% 1.10/1.32      (![X0 : $i]:
% 1.10/1.32         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32          | ~ (l1_orders_2 @ sk_A)
% 1.10/1.32          | ~ (v5_orders_2 @ sk_A)
% 1.10/1.32          | ~ (v4_orders_2 @ sk_A)
% 1.10/1.32          | ~ (v3_orders_2 @ sk_A)
% 1.10/1.32          | (v2_struct_0 @ sk_A)
% 1.10/1.32          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 1.10/1.32               X0))),
% 1.10/1.32      inference('sup-', [status(thm)], ['121', '123'])).
% 1.10/1.32  thf('125', plain, ((l1_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('126', plain, ((v5_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('127', plain, ((v4_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('128', plain, ((v3_orders_2 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('129', plain,
% 1.10/1.32      (![X0 : $i]:
% 1.10/1.32         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32          | (v2_struct_0 @ sk_A)
% 1.10/1.32          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 1.10/1.32               X0))),
% 1.10/1.32      inference('demod', [status(thm)], ['124', '125', '126', '127', '128'])).
% 1.10/1.32  thf('130', plain,
% 1.10/1.32      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.10/1.32        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32        | (v2_struct_0 @ sk_A)
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('sup-', [status(thm)], ['120', '129'])).
% 1.10/1.32  thf('131', plain,
% 1.10/1.32      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 1.10/1.32         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.10/1.32      inference('split', [status(esa)], ['58'])).
% 1.10/1.32  thf('132', plain,
% 1.10/1.32      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 1.10/1.32       ((r2_hidden @ sk_C @ 
% 1.10/1.32         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.10/1.32      inference('split', [status(esa)], ['58'])).
% 1.10/1.32  thf('133', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.10/1.32      inference('sat_resolution*', [status(thm)], ['57', '114', '132'])).
% 1.10/1.32  thf('134', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 1.10/1.32      inference('simpl_trail', [status(thm)], ['131', '133'])).
% 1.10/1.32  thf('135', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('136', plain,
% 1.10/1.32      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32        | (v2_struct_0 @ sk_A)
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('demod', [status(thm)], ['130', '134', '135'])).
% 1.10/1.32  thf('137', plain,
% 1.10/1.32      (((v2_struct_0 @ sk_A)
% 1.10/1.32        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('simplify', [status(thm)], ['136'])).
% 1.10/1.32  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('139', plain,
% 1.10/1.32      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.10/1.32      inference('clc', [status(thm)], ['137', '138'])).
% 1.10/1.32  thf('140', plain,
% 1.10/1.32      ((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 1.10/1.32        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.10/1.32      inference('simpl_trail', [status(thm)], ['56', '115'])).
% 1.10/1.32  thf('141', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.10/1.32      inference('clc', [status(thm)], ['139', '140'])).
% 1.10/1.32  thf('142', plain,
% 1.10/1.32      (![X0 : $i]:
% 1.10/1.32         ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.10/1.32      inference('demod', [status(thm)], ['30', '141'])).
% 1.10/1.32  thf('143', plain,
% 1.10/1.32      (((v2_struct_0 @ sk_A)
% 1.10/1.32        | (r2_hidden @ sk_B @ 
% 1.10/1.32           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.10/1.32      inference('clc', [status(thm)], ['27', '142'])).
% 1.10/1.32  thf('144', plain, (~ (v2_struct_0 @ sk_A)),
% 1.10/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.32  thf('145', plain,
% 1.10/1.32      ((r2_hidden @ sk_B @ 
% 1.10/1.32        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.10/1.32      inference('clc', [status(thm)], ['143', '144'])).
% 1.10/1.32  thf('146', plain,
% 1.10/1.32      (![X0 : $i]:
% 1.10/1.32         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.10/1.32          | ~ (r2_hidden @ X0 @ 
% 1.10/1.32               (k1_orders_2 @ sk_A @ 
% 1.10/1.32                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.10/1.32      inference('sup-', [status(thm)], ['110', '111'])).
% 1.10/1.32  thf('147', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.10/1.32      inference('clc', [status(thm)], ['139', '140'])).
% 1.10/1.32  thf('148', plain,
% 1.10/1.32      (![X0 : $i]:
% 1.10/1.32         ~ (r2_hidden @ X0 @ 
% 1.10/1.32            (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.10/1.32      inference('demod', [status(thm)], ['146', '147'])).
% 1.10/1.32  thf('149', plain, ($false), inference('sup-', [status(thm)], ['145', '148'])).
% 1.10/1.32  
% 1.10/1.32  % SZS output end Refutation
% 1.10/1.32  
% 1.10/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
