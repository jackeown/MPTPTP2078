%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0FNJnq5KV0

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:58 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  173 (1348 expanded)
%              Number of leaves         :   31 ( 392 expanded)
%              Depth                    :   35
%              Number of atoms          : 1825 (25670 expanded)
%              Number of equality atoms :   42 ( 188 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X25 ) @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r2_hidden @ X20 @ ( a_2_1_orders_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X17 ) )
      | ( X20 != X21 )
      | ( r2_hidden @ ( sk_E @ X21 @ X18 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('10',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( r2_hidden @ ( sk_E @ X21 @ X18 @ X17 ) @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_struct_0 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
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
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

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

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k2_orders_2 @ X14 @ X13 )
        = ( a_2_1_orders_2 @ X14 @ X13 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('18',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
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
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('35',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('37',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( X20
        = ( sk_D_1 @ X18 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ ( a_2_1_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('41',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B
      = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,
    ( ( ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['35','48'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('50',plain,(
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

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('52',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('55',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('56',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('58',plain,
    ( ( ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('60',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('61',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r2_orders_2 @ X17 @ ( sk_D_1 @ X18 @ X17 @ X20 ) @ X19 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( a_2_1_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('63',plain,(
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
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['53','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['49','75'])).

thf('77',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(dt_k2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('81',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_orders_2])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
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

thf('87',plain,
    ( ( m1_subset_1 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('90',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['79','91'])).

thf('93',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','92'])).

thf('94',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','93'])).

thf('95',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simpl_trail,[status(thm)],['29','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['27','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('100',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('103',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('104',plain,(
    r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('105',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('109',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('110',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('115',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r2_hidden @ X20 @ ( a_2_1_orders_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X17 ) )
      | ( X20 != X21 )
      | ~ ( r2_orders_2 @ X17 @ X21 @ ( sk_E @ X21 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('116',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ~ ( r2_orders_2 @ X17 @ X21 @ ( sk_E @ X21 @ X18 @ X17 ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X17 ) )
      | ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v2_struct_0 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
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
    inference('sup-',[status(thm)],['114','116'])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['31'])).

thf('125',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('126',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['30','93','125'])).

thf('127',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['124','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('134',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['28'])).

thf('135',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','93'])).

thf('137',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['135','136'])).

thf('138',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['132','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['101','138'])).

thf('140',plain,(
    $false ),
    inference('sup-',[status(thm)],['98','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0FNJnq5KV0
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.06/1.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.25  % Solved by: fo/fo7.sh
% 1.06/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.25  % done 1431 iterations in 0.798s
% 1.06/1.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.25  % SZS output start Refutation
% 1.06/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.25  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.25  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.06/1.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.25  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.06/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.25  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 1.06/1.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.06/1.25  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 1.06/1.25  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.06/1.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.25  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.06/1.25  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.06/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.25  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 1.06/1.25  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 1.06/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.25  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.06/1.25  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 1.06/1.25  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.06/1.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.25  thf(t52_orders_2, conjecture,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.06/1.25         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.25           ( ![C:$i]:
% 1.06/1.25             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.25               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 1.06/1.25                 ( r2_hidden @
% 1.06/1.25                   B @ 
% 1.06/1.25                   ( k2_orders_2 @
% 1.06/1.25                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 1.06/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.25    (~( ![A:$i]:
% 1.06/1.25        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.06/1.25            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.06/1.25          ( ![B:$i]:
% 1.06/1.25            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.25              ( ![C:$i]:
% 1.06/1.25                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.25                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 1.06/1.25                    ( r2_hidden @
% 1.06/1.25                      B @ 
% 1.06/1.25                      ( k2_orders_2 @
% 1.06/1.25                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 1.06/1.25    inference('cnf.neg', [status(esa)], [t52_orders_2])).
% 1.06/1.25  thf('0', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('1', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf(t35_orders_2, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.06/1.25           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 1.06/1.25             ( m1_subset_1 @
% 1.06/1.25               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.06/1.25               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.06/1.25  thf('2', plain,
% 1.06/1.25      (![X24 : $i, X25 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 1.06/1.25          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X25) @ X24) @ 
% 1.06/1.25             (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.06/1.25          | ~ (l1_orders_2 @ X25)
% 1.06/1.25          | ~ (v3_orders_2 @ X25)
% 1.06/1.25          | (v2_struct_0 @ X25))),
% 1.06/1.25      inference('cnf', [status(esa)], [t35_orders_2])).
% 1.06/1.25  thf('3', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (v3_orders_2 @ sk_A)
% 1.06/1.25        | ~ (l1_orders_2 @ sk_A)
% 1.06/1.25        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.06/1.25           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.25  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('6', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.06/1.25           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.06/1.25      inference('demod', [status(thm)], ['3', '4', '5'])).
% 1.06/1.25  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('8', plain,
% 1.06/1.25      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.06/1.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.25  thf(fraenkel_a_2_1_orders_2, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 1.06/1.25         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 1.06/1.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 1.06/1.25       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 1.06/1.25         ( ?[D:$i]:
% 1.06/1.25           ( ( ![E:$i]:
% 1.06/1.25               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.06/1.25                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 1.06/1.25             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.06/1.25  thf('9', plain,
% 1.06/1.25      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 1.06/1.25         (~ (l1_orders_2 @ X17)
% 1.06/1.25          | ~ (v5_orders_2 @ X17)
% 1.06/1.25          | ~ (v4_orders_2 @ X17)
% 1.06/1.25          | ~ (v3_orders_2 @ X17)
% 1.06/1.25          | (v2_struct_0 @ X17)
% 1.06/1.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.06/1.25          | (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18))
% 1.06/1.25          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X17))
% 1.06/1.25          | ((X20) != (X21))
% 1.06/1.25          | (r2_hidden @ (sk_E @ X21 @ X18 @ X17) @ X18))),
% 1.06/1.25      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.06/1.25  thf('10', plain,
% 1.06/1.25      (![X17 : $i, X18 : $i, X21 : $i]:
% 1.06/1.25         ((r2_hidden @ (sk_E @ X21 @ X18 @ X17) @ X18)
% 1.06/1.25          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X17))
% 1.06/1.25          | (r2_hidden @ X21 @ (a_2_1_orders_2 @ X17 @ X18))
% 1.06/1.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.06/1.25          | (v2_struct_0 @ X17)
% 1.06/1.25          | ~ (v3_orders_2 @ X17)
% 1.06/1.25          | ~ (v4_orders_2 @ X17)
% 1.06/1.25          | ~ (v5_orders_2 @ X17)
% 1.06/1.25          | ~ (l1_orders_2 @ X17))),
% 1.06/1.25      inference('simplify', [status(thm)], ['9'])).
% 1.06/1.25  thf('11', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (l1_orders_2 @ sk_A)
% 1.06/1.25          | ~ (v5_orders_2 @ sk_A)
% 1.06/1.25          | ~ (v4_orders_2 @ sk_A)
% 1.06/1.25          | ~ (v3_orders_2 @ sk_A)
% 1.06/1.25          | (v2_struct_0 @ sk_A)
% 1.06/1.25          | (r2_hidden @ X0 @ 
% 1.06/1.25             (a_2_1_orders_2 @ sk_A @ 
% 1.06/1.25              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | (r2_hidden @ 
% 1.06/1.25             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 1.06/1.25             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['8', '10'])).
% 1.06/1.25  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('13', plain, ((v5_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('16', plain,
% 1.06/1.25      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.06/1.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.25  thf(d13_orders_2, axiom,
% 1.06/1.25    (![A:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.06/1.25         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.06/1.25       ( ![B:$i]:
% 1.06/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.25           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 1.06/1.25  thf('17', plain,
% 1.06/1.25      (![X13 : $i, X14 : $i]:
% 1.06/1.25         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.06/1.25          | ((k2_orders_2 @ X14 @ X13) = (a_2_1_orders_2 @ X14 @ X13))
% 1.06/1.25          | ~ (l1_orders_2 @ X14)
% 1.06/1.25          | ~ (v5_orders_2 @ X14)
% 1.06/1.25          | ~ (v4_orders_2 @ X14)
% 1.06/1.25          | ~ (v3_orders_2 @ X14)
% 1.06/1.25          | (v2_struct_0 @ X14))),
% 1.06/1.25      inference('cnf', [status(esa)], [d13_orders_2])).
% 1.06/1.25  thf('18', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (v3_orders_2 @ sk_A)
% 1.06/1.25        | ~ (v4_orders_2 @ sk_A)
% 1.06/1.25        | ~ (v5_orders_2 @ sk_A)
% 1.06/1.25        | ~ (l1_orders_2 @ sk_A)
% 1.06/1.25        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.06/1.25            = (a_2_1_orders_2 @ sk_A @ 
% 1.06/1.25               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['16', '17'])).
% 1.06/1.25  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('23', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.06/1.25            = (a_2_1_orders_2 @ sk_A @ 
% 1.06/1.25               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.06/1.25      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 1.06/1.25  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('25', plain,
% 1.06/1.25      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.06/1.25         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['23', '24'])).
% 1.06/1.25  thf('26', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v2_struct_0 @ sk_A)
% 1.06/1.25          | (r2_hidden @ X0 @ 
% 1.06/1.25             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | (r2_hidden @ 
% 1.06/1.25             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 1.06/1.25             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.06/1.25      inference('demod', [status(thm)], ['11', '12', '13', '14', '15', '25'])).
% 1.06/1.25  thf('27', plain,
% 1.06/1.25      (((r2_hidden @ 
% 1.06/1.25         (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 1.06/1.25         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.06/1.25        | (r2_hidden @ sk_B @ 
% 1.06/1.25           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['0', '26'])).
% 1.06/1.25  thf('28', plain,
% 1.06/1.25      ((~ (r2_hidden @ sk_B @ 
% 1.06/1.25           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.06/1.25        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('29', plain,
% 1.06/1.25      ((~ (r2_hidden @ sk_B @ 
% 1.06/1.25           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('split', [status(esa)], ['28'])).
% 1.06/1.25  thf('30', plain,
% 1.06/1.25      (~
% 1.06/1.25       ((r2_hidden @ sk_B @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 1.06/1.25       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.06/1.25      inference('split', [status(esa)], ['28'])).
% 1.06/1.25  thf('31', plain,
% 1.06/1.25      (((r2_hidden @ sk_B @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.06/1.25        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('32', plain,
% 1.06/1.25      (((r2_hidden @ sk_B @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('split', [status(esa)], ['31'])).
% 1.06/1.25  thf('33', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf(redefinition_k6_domain_1, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.06/1.25       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.06/1.25  thf('34', plain,
% 1.06/1.25      (![X22 : $i, X23 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ X22)
% 1.06/1.25          | ~ (m1_subset_1 @ X23 @ X22)
% 1.06/1.25          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 1.06/1.25      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.06/1.25  thf('35', plain,
% 1.06/1.25      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.25  thf('36', plain,
% 1.06/1.25      (((r2_hidden @ sk_B @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('split', [status(esa)], ['31'])).
% 1.06/1.25  thf('37', plain,
% 1.06/1.25      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.06/1.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.25  thf('38', plain,
% 1.06/1.25      (![X17 : $i, X18 : $i, X20 : $i]:
% 1.06/1.25         (~ (l1_orders_2 @ X17)
% 1.06/1.25          | ~ (v5_orders_2 @ X17)
% 1.06/1.25          | ~ (v4_orders_2 @ X17)
% 1.06/1.25          | ~ (v3_orders_2 @ X17)
% 1.06/1.25          | (v2_struct_0 @ X17)
% 1.06/1.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.06/1.25          | ((X20) = (sk_D_1 @ X18 @ X17 @ X20))
% 1.06/1.25          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 1.06/1.25      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.06/1.25  thf('39', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X0 @ 
% 1.06/1.25             (a_2_1_orders_2 @ sk_A @ 
% 1.06/1.25              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.06/1.25          | ((X0)
% 1.06/1.25              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ 
% 1.06/1.25                 X0))
% 1.06/1.25          | (v2_struct_0 @ sk_A)
% 1.06/1.25          | ~ (v3_orders_2 @ sk_A)
% 1.06/1.25          | ~ (v4_orders_2 @ sk_A)
% 1.06/1.25          | ~ (v5_orders_2 @ sk_A)
% 1.06/1.25          | ~ (l1_orders_2 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['37', '38'])).
% 1.06/1.25  thf('40', plain,
% 1.06/1.25      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.06/1.25         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['23', '24'])).
% 1.06/1.25  thf('41', plain, ((v3_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('42', plain, ((v4_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('43', plain, ((v5_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('44', plain, ((l1_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('45', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X0 @ 
% 1.06/1.25             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 1.06/1.25          | ((X0)
% 1.06/1.25              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ 
% 1.06/1.25                 X0))
% 1.06/1.25          | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['39', '40', '41', '42', '43', '44'])).
% 1.06/1.25  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('47', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (((X0)
% 1.06/1.25            = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ X0))
% 1.06/1.25          | ~ (r2_hidden @ X0 @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.06/1.25      inference('clc', [status(thm)], ['45', '46'])).
% 1.06/1.25  thf('48', plain,
% 1.06/1.25      ((((sk_B)
% 1.06/1.25          = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ sk_B)))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['36', '47'])).
% 1.06/1.25  thf('49', plain,
% 1.06/1.25      (((((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))
% 1.06/1.25         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('sup+', [status(thm)], ['35', '48'])).
% 1.06/1.25  thf(t69_enumset1, axiom,
% 1.06/1.25    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.06/1.25  thf('50', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.06/1.25  thf(d2_tarski, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.06/1.25       ( ![D:$i]:
% 1.06/1.25         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.06/1.25  thf('51', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.06/1.25         (((X1) != (X0))
% 1.06/1.25          | (r2_hidden @ X1 @ X2)
% 1.06/1.25          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 1.06/1.25      inference('cnf', [status(esa)], [d2_tarski])).
% 1.06/1.25  thf('52', plain,
% 1.06/1.25      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 1.06/1.25      inference('simplify', [status(thm)], ['51'])).
% 1.06/1.25  thf('53', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.06/1.25      inference('sup+', [status(thm)], ['50', '52'])).
% 1.06/1.25  thf('54', plain,
% 1.06/1.25      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.25  thf('55', plain,
% 1.06/1.25      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.06/1.25         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['23', '24'])).
% 1.06/1.25  thf('56', plain,
% 1.06/1.25      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.06/1.25          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['54', '55'])).
% 1.06/1.25  thf('57', plain,
% 1.06/1.25      (((r2_hidden @ sk_B @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('split', [status(esa)], ['31'])).
% 1.06/1.25  thf('58', plain,
% 1.06/1.25      ((((r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('sup+', [status(thm)], ['56', '57'])).
% 1.06/1.25  thf('59', plain,
% 1.06/1.25      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.25  thf('60', plain,
% 1.06/1.25      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.06/1.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.25  thf('61', plain,
% 1.06/1.25      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 1.06/1.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['59', '60'])).
% 1.06/1.25  thf('62', plain,
% 1.06/1.25      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.06/1.25         (~ (l1_orders_2 @ X17)
% 1.06/1.25          | ~ (v5_orders_2 @ X17)
% 1.06/1.25          | ~ (v4_orders_2 @ X17)
% 1.06/1.25          | ~ (v3_orders_2 @ X17)
% 1.06/1.25          | (v2_struct_0 @ X17)
% 1.06/1.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.06/1.25          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 1.06/1.25          | (r2_orders_2 @ X17 @ (sk_D_1 @ X18 @ X17 @ X20) @ X19)
% 1.06/1.25          | ~ (r2_hidden @ X19 @ X18)
% 1.06/1.25          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 1.06/1.25      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.06/1.25  thf('63', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 1.06/1.25          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 1.06/1.25             X1)
% 1.06/1.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | (v2_struct_0 @ sk_A)
% 1.06/1.25          | ~ (v3_orders_2 @ sk_A)
% 1.06/1.25          | ~ (v4_orders_2 @ sk_A)
% 1.06/1.25          | ~ (v5_orders_2 @ sk_A)
% 1.06/1.25          | ~ (l1_orders_2 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['61', '62'])).
% 1.06/1.25  thf('64', plain, ((v3_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('65', plain, ((v4_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('66', plain, ((v5_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('68', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 1.06/1.25          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 1.06/1.25             X1)
% 1.06/1.25          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 1.06/1.25  thf('69', plain,
% 1.06/1.25      ((![X0 : $i]:
% 1.06/1.25          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25           | (v2_struct_0 @ sk_A)
% 1.06/1.25           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25           | (r2_orders_2 @ sk_A @ 
% 1.06/1.25              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 1.06/1.25           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 1.06/1.25           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['58', '68'])).
% 1.06/1.25  thf('70', plain,
% 1.06/1.25      ((![X0 : $i]:
% 1.06/1.25          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 1.06/1.25           | (r2_orders_2 @ sk_A @ 
% 1.06/1.25              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 1.06/1.25           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25           | (v2_struct_0 @ sk_A)
% 1.06/1.25           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('simplify', [status(thm)], ['69'])).
% 1.06/1.25  thf('71', plain,
% 1.06/1.25      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25         | (v2_struct_0 @ sk_A)
% 1.06/1.25         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.06/1.25         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 1.06/1.25            sk_C)))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['53', '70'])).
% 1.06/1.25  thf('72', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('73', plain,
% 1.06/1.25      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25         | (v2_struct_0 @ sk_A)
% 1.06/1.25         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 1.06/1.25            sk_C)))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('demod', [status(thm)], ['71', '72'])).
% 1.06/1.25  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('75', plain,
% 1.06/1.25      ((((r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 1.06/1.25          sk_C)
% 1.06/1.25         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('clc', [status(thm)], ['73', '74'])).
% 1.06/1.25  thf('76', plain,
% 1.06/1.25      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 1.06/1.25         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('sup+', [status(thm)], ['49', '75'])).
% 1.06/1.25  thf('77', plain,
% 1.06/1.25      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 1.06/1.25         <= (((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('simplify', [status(thm)], ['76'])).
% 1.06/1.25  thf('78', plain,
% 1.06/1.25      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 1.06/1.25         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.06/1.25      inference('split', [status(esa)], ['28'])).
% 1.06/1.25  thf('79', plain,
% 1.06/1.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.06/1.25         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 1.06/1.25             ((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['77', '78'])).
% 1.06/1.25  thf('80', plain,
% 1.06/1.25      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.06/1.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.25  thf(dt_k2_orders_2, axiom,
% 1.06/1.25    (![A:$i,B:$i]:
% 1.06/1.25     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.06/1.25         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 1.06/1.25         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.25       ( m1_subset_1 @
% 1.06/1.25         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.25  thf('81', plain,
% 1.06/1.25      (![X15 : $i, X16 : $i]:
% 1.06/1.25         (~ (l1_orders_2 @ X15)
% 1.06/1.25          | ~ (v5_orders_2 @ X15)
% 1.06/1.25          | ~ (v4_orders_2 @ X15)
% 1.06/1.25          | ~ (v3_orders_2 @ X15)
% 1.06/1.25          | (v2_struct_0 @ X15)
% 1.06/1.25          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.06/1.25          | (m1_subset_1 @ (k2_orders_2 @ X15 @ X16) @ 
% 1.06/1.25             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 1.06/1.25      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 1.06/1.25  thf('82', plain,
% 1.06/1.25      (((m1_subset_1 @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.25        | (v2_struct_0 @ sk_A)
% 1.06/1.25        | ~ (v3_orders_2 @ sk_A)
% 1.06/1.25        | ~ (v4_orders_2 @ sk_A)
% 1.06/1.25        | ~ (v5_orders_2 @ sk_A)
% 1.06/1.25        | ~ (l1_orders_2 @ sk_A))),
% 1.06/1.25      inference('sup-', [status(thm)], ['80', '81'])).
% 1.06/1.25  thf('83', plain, ((v3_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('84', plain, ((v4_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('85', plain, ((v5_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('86', plain, ((l1_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('87', plain,
% 1.06/1.25      (((m1_subset_1 @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.06/1.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.25        | (v2_struct_0 @ sk_A))),
% 1.06/1.25      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 1.06/1.25  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('89', plain,
% 1.06/1.25      ((m1_subset_1 @ 
% 1.06/1.25        (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 1.06/1.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['87', '88'])).
% 1.06/1.25  thf(t5_subset, axiom,
% 1.06/1.25    (![A:$i,B:$i,C:$i]:
% 1.06/1.25     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.06/1.25          ( v1_xboole_0 @ C ) ) ))).
% 1.06/1.25  thf('90', plain,
% 1.06/1.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X10 @ X11)
% 1.06/1.25          | ~ (v1_xboole_0 @ X12)
% 1.06/1.25          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t5_subset])).
% 1.06/1.25  thf('91', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | ~ (r2_hidden @ X0 @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['89', '90'])).
% 1.06/1.25  thf('92', plain,
% 1.06/1.25      ((![X0 : $i]:
% 1.06/1.25          ~ (r2_hidden @ X0 @ 
% 1.06/1.25             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 1.06/1.25         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 1.06/1.25             ((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['79', '91'])).
% 1.06/1.25  thf('93', plain,
% 1.06/1.25      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 1.06/1.25       ~
% 1.06/1.25       ((r2_hidden @ sk_B @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['32', '92'])).
% 1.06/1.25  thf('94', plain,
% 1.06/1.25      (~
% 1.06/1.25       ((r2_hidden @ sk_B @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.06/1.25      inference('sat_resolution*', [status(thm)], ['30', '93'])).
% 1.06/1.25  thf('95', plain,
% 1.06/1.25      (~ (r2_hidden @ sk_B @ 
% 1.06/1.25          (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.06/1.25      inference('simpl_trail', [status(thm)], ['29', '94'])).
% 1.06/1.25  thf('96', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | (r2_hidden @ 
% 1.06/1.25           (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 1.06/1.25           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.06/1.25      inference('clc', [status(thm)], ['27', '95'])).
% 1.06/1.25  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('98', plain,
% 1.06/1.25      ((r2_hidden @ 
% 1.06/1.25        (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 1.06/1.25        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 1.06/1.25      inference('clc', [status(thm)], ['96', '97'])).
% 1.06/1.25  thf('99', plain,
% 1.06/1.25      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 1.06/1.25        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('clc', [status(thm)], ['6', '7'])).
% 1.06/1.25  thf('100', plain,
% 1.06/1.25      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X10 @ X11)
% 1.06/1.25          | ~ (v1_xboole_0 @ X12)
% 1.06/1.25          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.06/1.25      inference('cnf', [status(esa)], [t5_subset])).
% 1.06/1.25  thf('101', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['99', '100'])).
% 1.06/1.25  thf('102', plain,
% 1.06/1.25      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.25  thf('103', plain,
% 1.06/1.25      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.25  thf('104', plain,
% 1.06/1.25      ((r2_hidden @ 
% 1.06/1.25        (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A) @ 
% 1.06/1.25        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 1.06/1.25      inference('clc', [status(thm)], ['96', '97'])).
% 1.06/1.25  thf('105', plain,
% 1.06/1.25      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 1.06/1.25         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['103', '104'])).
% 1.06/1.25  thf('106', plain,
% 1.06/1.25      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 1.06/1.25         (k1_tarski @ sk_C))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['102', '105'])).
% 1.06/1.25  thf('107', plain,
% 1.06/1.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25        | (r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 1.06/1.25           (k1_tarski @ sk_C)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['106'])).
% 1.06/1.25  thf('108', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 1.06/1.25      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.06/1.25  thf('109', plain,
% 1.06/1.25      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X4 @ X2)
% 1.06/1.25          | ((X4) = (X3))
% 1.06/1.25          | ((X4) = (X0))
% 1.06/1.25          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 1.06/1.25      inference('cnf', [status(esa)], [d2_tarski])).
% 1.06/1.25  thf('110', plain,
% 1.06/1.25      (![X0 : $i, X3 : $i, X4 : $i]:
% 1.06/1.25         (((X4) = (X0))
% 1.06/1.25          | ((X4) = (X3))
% 1.06/1.25          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['109'])).
% 1.06/1.25  thf('111', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['108', '110'])).
% 1.06/1.25  thf('112', plain,
% 1.06/1.25      (![X0 : $i, X1 : $i]:
% 1.06/1.25         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['111'])).
% 1.06/1.25  thf('113', plain,
% 1.06/1.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['107', '112'])).
% 1.06/1.25  thf('114', plain,
% 1.06/1.25      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 1.06/1.25         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['59', '60'])).
% 1.06/1.25  thf('115', plain,
% 1.06/1.25      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 1.06/1.25         (~ (l1_orders_2 @ X17)
% 1.06/1.25          | ~ (v5_orders_2 @ X17)
% 1.06/1.25          | ~ (v4_orders_2 @ X17)
% 1.06/1.25          | ~ (v3_orders_2 @ X17)
% 1.06/1.25          | (v2_struct_0 @ X17)
% 1.06/1.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.06/1.25          | (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18))
% 1.06/1.25          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X17))
% 1.06/1.25          | ((X20) != (X21))
% 1.06/1.25          | ~ (r2_orders_2 @ X17 @ X21 @ (sk_E @ X21 @ X18 @ X17)))),
% 1.06/1.25      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.06/1.25  thf('116', plain,
% 1.06/1.25      (![X17 : $i, X18 : $i, X21 : $i]:
% 1.06/1.25         (~ (r2_orders_2 @ X17 @ X21 @ (sk_E @ X21 @ X18 @ X17))
% 1.06/1.25          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X17))
% 1.06/1.25          | (r2_hidden @ X21 @ (a_2_1_orders_2 @ X17 @ X18))
% 1.06/1.25          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.06/1.25          | (v2_struct_0 @ X17)
% 1.06/1.25          | ~ (v3_orders_2 @ X17)
% 1.06/1.25          | ~ (v4_orders_2 @ X17)
% 1.06/1.25          | ~ (v5_orders_2 @ X17)
% 1.06/1.25          | ~ (l1_orders_2 @ X17))),
% 1.06/1.25      inference('simplify', [status(thm)], ['115'])).
% 1.06/1.25  thf('117', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | ~ (l1_orders_2 @ sk_A)
% 1.06/1.25          | ~ (v5_orders_2 @ sk_A)
% 1.06/1.25          | ~ (v4_orders_2 @ sk_A)
% 1.06/1.25          | ~ (v3_orders_2 @ sk_A)
% 1.06/1.25          | (v2_struct_0 @ sk_A)
% 1.06/1.25          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 1.06/1.25               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['114', '116'])).
% 1.06/1.25  thf('118', plain, ((l1_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('119', plain, ((v5_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('120', plain, ((v4_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('121', plain, ((v3_orders_2 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('122', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | (v2_struct_0 @ sk_A)
% 1.06/1.25          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 1.06/1.25               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 1.06/1.25      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 1.06/1.25  thf('123', plain,
% 1.06/1.25      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 1.06/1.25        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25        | (v2_struct_0 @ sk_A)
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup-', [status(thm)], ['113', '122'])).
% 1.06/1.25  thf('124', plain,
% 1.06/1.25      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 1.06/1.25         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 1.06/1.25      inference('split', [status(esa)], ['31'])).
% 1.06/1.25  thf('125', plain,
% 1.06/1.25      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 1.06/1.25       ((r2_hidden @ sk_B @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.06/1.25      inference('split', [status(esa)], ['31'])).
% 1.06/1.25  thf('126', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 1.06/1.25      inference('sat_resolution*', [status(thm)], ['30', '93', '125'])).
% 1.06/1.25  thf('127', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 1.06/1.25      inference('simpl_trail', [status(thm)], ['124', '126'])).
% 1.06/1.25  thf('128', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('129', plain,
% 1.06/1.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25        | (v2_struct_0 @ sk_A)
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('demod', [status(thm)], ['123', '127', '128'])).
% 1.06/1.25  thf('130', plain,
% 1.06/1.25      (((v2_struct_0 @ sk_A)
% 1.06/1.25        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('simplify', [status(thm)], ['129'])).
% 1.06/1.25  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 1.06/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.25  thf('132', plain,
% 1.06/1.25      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.06/1.25        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 1.06/1.25      inference('clc', [status(thm)], ['130', '131'])).
% 1.06/1.25  thf('133', plain,
% 1.06/1.25      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 1.06/1.25          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('sup+', [status(thm)], ['54', '55'])).
% 1.06/1.25  thf('134', plain,
% 1.06/1.25      ((~ (r2_hidden @ sk_B @ 
% 1.06/1.25           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('split', [status(esa)], ['28'])).
% 1.06/1.25  thf('135', plain,
% 1.06/1.25      (((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.06/1.25         <= (~
% 1.06/1.25             ((r2_hidden @ sk_B @ 
% 1.06/1.25               (k2_orders_2 @ sk_A @ 
% 1.06/1.25                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 1.06/1.25      inference('sup-', [status(thm)], ['133', '134'])).
% 1.06/1.25  thf('136', plain,
% 1.06/1.25      (~
% 1.06/1.25       ((r2_hidden @ sk_B @ 
% 1.06/1.25         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 1.06/1.25      inference('sat_resolution*', [status(thm)], ['30', '93'])).
% 1.06/1.25  thf('137', plain,
% 1.06/1.25      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 1.06/1.25        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.25      inference('simpl_trail', [status(thm)], ['135', '136'])).
% 1.06/1.25  thf('138', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.06/1.25      inference('clc', [status(thm)], ['132', '137'])).
% 1.06/1.25  thf('139', plain,
% 1.06/1.25      (![X0 : $i]:
% 1.06/1.25         ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))),
% 1.06/1.25      inference('demod', [status(thm)], ['101', '138'])).
% 1.06/1.25  thf('140', plain, ($false), inference('sup-', [status(thm)], ['98', '139'])).
% 1.06/1.25  
% 1.06/1.25  % SZS output end Refutation
% 1.06/1.25  
% 1.06/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
