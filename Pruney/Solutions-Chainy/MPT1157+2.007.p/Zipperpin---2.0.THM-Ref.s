%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YxfoWg7RM0

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:57 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  176 (1660 expanded)
%              Number of leaves         :   31 ( 484 expanded)
%              Depth                    :   38
%              Number of atoms          : 1884 (32150 expanded)
%              Number of equality atoms :   42 ( 216 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
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

thf('10',plain,(
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
    ( ( r2_hidden @ ( sk_E @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14','15','25'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_hidden @ ( sk_E @ sk_B @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('38',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('45',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_C
      = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,
    ( ( ( sk_C
        = ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','52'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('54',plain,(
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

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('56',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf('58',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('59',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('60',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['39'])).

thf('62',plain,
    ( ( ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('64',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('65',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
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

thf('67',plain,(
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
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['53','79'])).

thf('81',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['28'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('85',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['35','87'])).

thf(t48_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('89',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_orders_2 @ X22 @ ( k6_domain_1 @ ( u1_struct_0 @ X22 ) @ X21 ) ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_orders_2])).

thf('90',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','98'])).

thf('100',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['29','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r2_hidden @ ( sk_E @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('105',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('106',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('107',plain,(
    r2_hidden @ ( sk_E @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('108',plain,
    ( ( r2_hidden @ ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( r2_hidden @ ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['105','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('112',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('113',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('118',plain,(
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

thf('119',plain,(
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
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
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
    inference('sup-',[status(thm)],['117','119'])).

thf('121',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','125'])).

thf('127',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['39'])).

thf('128',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['39'])).

thf('129',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['30','98','128'])).

thf('130',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['127','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','130','131'])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('137',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['28'])).

thf('138',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['30','98'])).

thf('140',plain,
    ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['138','139'])).

thf('141',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['135','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','141'])).

thf('143',plain,(
    $false ),
    inference('sup-',[status(thm)],['103','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YxfoWg7RM0
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:41:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.65/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.65/0.86  % Solved by: fo/fo7.sh
% 0.65/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.86  % done 688 iterations in 0.390s
% 0.65/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.65/0.86  % SZS output start Refutation
% 0.65/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.86  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.65/0.86  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.65/0.86  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.65/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.65/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.65/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.65/0.86  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 0.65/0.86  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.65/0.86  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.65/0.86  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.65/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.86  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.65/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.65/0.86  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.65/0.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.65/0.86  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.65/0.86  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.65/0.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.65/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.86  thf(t51_orders_2, conjecture,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.65/0.86         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.65/0.86       ( ![B:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86           ( ![C:$i]:
% 0.65/0.86             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.65/0.86                 ( r2_hidden @
% 0.65/0.86                   C @ 
% 0.65/0.86                   ( k1_orders_2 @
% 0.65/0.86                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ))).
% 0.65/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.86    (~( ![A:$i]:
% 0.65/0.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.65/0.86            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.65/0.86          ( ![B:$i]:
% 0.65/0.86            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86              ( ![C:$i]:
% 0.65/0.86                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.65/0.86                    ( r2_hidden @
% 0.65/0.86                      C @ 
% 0.65/0.86                      ( k1_orders_2 @
% 0.65/0.86                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ) )),
% 0.65/0.86    inference('cnf.neg', [status(esa)], [t51_orders_2])).
% 0.65/0.86  thf('0', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(t35_orders_2, axiom,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.65/0.86       ( ![B:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.65/0.86             ( m1_subset_1 @
% 0.65/0.86               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.65/0.86               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.65/0.86  thf('2', plain,
% 0.65/0.86      (![X19 : $i, X20 : $i]:
% 0.65/0.86         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.65/0.86          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X20) @ X19) @ 
% 0.65/0.86             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.65/0.86          | ~ (l1_orders_2 @ X20)
% 0.65/0.86          | ~ (v3_orders_2 @ X20)
% 0.65/0.86          | (v2_struct_0 @ X20))),
% 0.65/0.86      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.65/0.86  thf('3', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86        | ~ (l1_orders_2 @ sk_A)
% 0.65/0.86        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.65/0.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['1', '2'])).
% 0.65/0.86  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('5', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('6', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.65/0.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.65/0.86      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.65/0.86  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('8', plain,
% 0.65/0.86      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.65/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('clc', [status(thm)], ['6', '7'])).
% 0.65/0.86  thf(fraenkel_a_2_0_orders_2, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i]:
% 0.65/0.86     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.65/0.86         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.65/0.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.65/0.86       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 0.65/0.86         ( ?[D:$i]:
% 0.65/0.86           ( ( ![E:$i]:
% 0.65/0.86               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.65/0.86                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 0.65/0.86             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.65/0.86  thf('9', plain,
% 0.65/0.86      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.65/0.86         (~ (l1_orders_2 @ X12)
% 0.65/0.86          | ~ (v5_orders_2 @ X12)
% 0.65/0.86          | ~ (v4_orders_2 @ X12)
% 0.65/0.86          | ~ (v3_orders_2 @ X12)
% 0.65/0.86          | (v2_struct_0 @ X12)
% 0.65/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.65/0.86          | (r2_hidden @ X15 @ (a_2_0_orders_2 @ X12 @ X13))
% 0.65/0.86          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.65/0.86          | ((X15) != (X16))
% 0.65/0.86          | (r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13))),
% 0.65/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.65/0.86  thf('10', plain,
% 0.65/0.86      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.65/0.86         ((r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13)
% 0.65/0.86          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.65/0.86          | (r2_hidden @ X16 @ (a_2_0_orders_2 @ X12 @ X13))
% 0.65/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.65/0.86          | (v2_struct_0 @ X12)
% 0.65/0.86          | ~ (v3_orders_2 @ X12)
% 0.65/0.86          | ~ (v4_orders_2 @ X12)
% 0.65/0.86          | ~ (v5_orders_2 @ X12)
% 0.65/0.86          | ~ (l1_orders_2 @ X12))),
% 0.65/0.86      inference('simplify', [status(thm)], ['9'])).
% 0.65/0.86  thf('11', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         (~ (l1_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | (r2_hidden @ X0 @ 
% 0.65/0.86             (a_2_0_orders_2 @ sk_A @ 
% 0.65/0.86              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (r2_hidden @ 
% 0.65/0.86             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.65/0.86             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['8', '10'])).
% 0.65/0.86  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('13', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('16', plain,
% 0.65/0.86      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.65/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('clc', [status(thm)], ['6', '7'])).
% 0.65/0.86  thf(d12_orders_2, axiom,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.65/0.86         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.65/0.86       ( ![B:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.86           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 0.65/0.86  thf('17', plain,
% 0.65/0.86      (![X10 : $i, X11 : $i]:
% 0.65/0.86         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.65/0.86          | ((k1_orders_2 @ X11 @ X10) = (a_2_0_orders_2 @ X11 @ X10))
% 0.65/0.86          | ~ (l1_orders_2 @ X11)
% 0.65/0.86          | ~ (v5_orders_2 @ X11)
% 0.65/0.86          | ~ (v4_orders_2 @ X11)
% 0.65/0.86          | ~ (v3_orders_2 @ X11)
% 0.65/0.86          | (v2_struct_0 @ X11))),
% 0.65/0.86      inference('cnf', [status(esa)], [d12_orders_2])).
% 0.65/0.86  thf('18', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86        | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86        | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86        | ~ (l1_orders_2 @ sk_A)
% 0.65/0.86        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.65/0.86            = (a_2_0_orders_2 @ sk_A @ 
% 0.65/0.86               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['16', '17'])).
% 0.65/0.86  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('23', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.65/0.86            = (a_2_0_orders_2 @ sk_A @ 
% 0.65/0.86               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.65/0.86      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.65/0.86  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('25', plain,
% 0.65/0.86      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.65/0.86         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('clc', [status(thm)], ['23', '24'])).
% 0.65/0.86  thf('26', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((v2_struct_0 @ sk_A)
% 0.65/0.86          | (r2_hidden @ X0 @ 
% 0.65/0.86             (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (r2_hidden @ 
% 0.65/0.86             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.65/0.86             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('demod', [status(thm)], ['11', '12', '13', '14', '15', '25'])).
% 0.65/0.86  thf('27', plain,
% 0.65/0.86      (((r2_hidden @ 
% 0.65/0.86         (sk_E @ sk_C @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.65/0.86         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.65/0.86        | (r2_hidden @ sk_C @ 
% 0.65/0.86           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86        | (v2_struct_0 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['0', '26'])).
% 0.65/0.86  thf('28', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_C @ 
% 0.65/0.86           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('29', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_C @ 
% 0.65/0.86           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.65/0.86         <= (~
% 0.65/0.86             ((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('split', [status(esa)], ['28'])).
% 0.65/0.86  thf('30', plain,
% 0.65/0.86      (~
% 0.65/0.86       ((r2_hidden @ sk_C @ 
% 0.65/0.86         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))) | 
% 0.65/0.86       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.86      inference('split', [status(esa)], ['28'])).
% 0.65/0.86  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('32', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((v2_struct_0 @ sk_A)
% 0.65/0.86          | (r2_hidden @ X0 @ 
% 0.65/0.86             (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (r2_hidden @ 
% 0.65/0.86             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.65/0.86             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('demod', [status(thm)], ['11', '12', '13', '14', '15', '25'])).
% 0.65/0.86  thf('33', plain,
% 0.65/0.86      (((r2_hidden @ 
% 0.65/0.86         (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.65/0.86         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.65/0.86        | (r2_hidden @ sk_B @ 
% 0.65/0.86           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86        | (v2_struct_0 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['31', '32'])).
% 0.65/0.86  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('35', plain,
% 0.65/0.86      (((r2_hidden @ sk_B @ 
% 0.65/0.86         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86        | (r2_hidden @ 
% 0.65/0.86           (sk_E @ sk_B @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.65/0.86           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('clc', [status(thm)], ['33', '34'])).
% 0.65/0.86  thf('36', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(redefinition_k6_domain_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.65/0.86       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.65/0.86  thf('37', plain,
% 0.65/0.86      (![X17 : $i, X18 : $i]:
% 0.65/0.86         ((v1_xboole_0 @ X17)
% 0.65/0.86          | ~ (m1_subset_1 @ X18 @ X17)
% 0.65/0.86          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.65/0.86      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.65/0.86  thf('38', plain,
% 0.65/0.86      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['36', '37'])).
% 0.65/0.86  thf('39', plain,
% 0.65/0.86      (((r2_hidden @ sk_C @ 
% 0.65/0.86         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('40', plain,
% 0.65/0.86      (((r2_hidden @ sk_C @ 
% 0.65/0.86         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('split', [status(esa)], ['39'])).
% 0.65/0.86  thf('41', plain,
% 0.65/0.86      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.65/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('clc', [status(thm)], ['6', '7'])).
% 0.65/0.86  thf('42', plain,
% 0.65/0.86      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.65/0.86         (~ (l1_orders_2 @ X12)
% 0.65/0.86          | ~ (v5_orders_2 @ X12)
% 0.65/0.86          | ~ (v4_orders_2 @ X12)
% 0.65/0.86          | ~ (v3_orders_2 @ X12)
% 0.65/0.86          | (v2_struct_0 @ X12)
% 0.65/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.65/0.86          | ((X15) = (sk_D_1 @ X13 @ X12 @ X15))
% 0.65/0.86          | ~ (r2_hidden @ X15 @ (a_2_0_orders_2 @ X12 @ X13)))),
% 0.65/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.65/0.86  thf('43', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X0 @ 
% 0.65/0.86             (a_2_0_orders_2 @ sk_A @ 
% 0.65/0.86              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86          | ((X0)
% 0.65/0.86              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ 
% 0.65/0.86                 X0))
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86          | ~ (l1_orders_2 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['41', '42'])).
% 0.65/0.86  thf('44', plain,
% 0.65/0.86      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.65/0.86         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('clc', [status(thm)], ['23', '24'])).
% 0.65/0.86  thf('45', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('46', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('47', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('48', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('49', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X0 @ 
% 0.65/0.86             (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86          | ((X0)
% 0.65/0.86              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ 
% 0.65/0.86                 X0))
% 0.65/0.86          | (v2_struct_0 @ sk_A))),
% 0.65/0.86      inference('demod', [status(thm)], ['43', '44', '45', '46', '47', '48'])).
% 0.65/0.86  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('51', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         (((X0)
% 0.65/0.86            = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ X0))
% 0.65/0.86          | ~ (r2_hidden @ X0 @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.65/0.86      inference('clc', [status(thm)], ['49', '50'])).
% 0.65/0.86  thf('52', plain,
% 0.65/0.86      ((((sk_C)
% 0.65/0.86          = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ sk_C)))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['40', '51'])).
% 0.65/0.86  thf('53', plain,
% 0.65/0.86      (((((sk_C) = (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.65/0.86         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['38', '52'])).
% 0.65/0.86  thf(t69_enumset1, axiom,
% 0.65/0.86    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.65/0.86  thf('54', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.65/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.86  thf(d2_tarski, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i]:
% 0.65/0.86     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.65/0.86       ( ![D:$i]:
% 0.65/0.86         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.65/0.86  thf('55', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.86         (((X1) != (X0))
% 0.65/0.86          | (r2_hidden @ X1 @ X2)
% 0.65/0.86          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [d2_tarski])).
% 0.65/0.86  thf('56', plain,
% 0.65/0.86      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.65/0.86      inference('simplify', [status(thm)], ['55'])).
% 0.65/0.86  thf('57', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['54', '56'])).
% 0.65/0.86  thf('58', plain,
% 0.65/0.86      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['36', '37'])).
% 0.65/0.86  thf('59', plain,
% 0.65/0.86      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.65/0.86         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('clc', [status(thm)], ['23', '24'])).
% 0.65/0.86  thf('60', plain,
% 0.65/0.86      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.65/0.86          = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['58', '59'])).
% 0.65/0.86  thf('61', plain,
% 0.65/0.86      (((r2_hidden @ sk_C @ 
% 0.65/0.86         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('split', [status(esa)], ['39'])).
% 0.65/0.86  thf('62', plain,
% 0.65/0.86      ((((r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['60', '61'])).
% 0.65/0.86  thf('63', plain,
% 0.65/0.86      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['36', '37'])).
% 0.65/0.86  thf('64', plain,
% 0.65/0.86      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.65/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('clc', [status(thm)], ['6', '7'])).
% 0.65/0.86  thf('65', plain,
% 0.65/0.86      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.65/0.86         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['63', '64'])).
% 0.65/0.86  thf('66', plain,
% 0.65/0.86      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.65/0.86         (~ (l1_orders_2 @ X12)
% 0.65/0.86          | ~ (v5_orders_2 @ X12)
% 0.65/0.86          | ~ (v4_orders_2 @ X12)
% 0.65/0.86          | ~ (v3_orders_2 @ X12)
% 0.65/0.86          | (v2_struct_0 @ X12)
% 0.65/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.65/0.86          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.65/0.86          | (r2_orders_2 @ X12 @ X14 @ (sk_D_1 @ X13 @ X12 @ X15))
% 0.65/0.86          | ~ (r2_hidden @ X14 @ X13)
% 0.65/0.86          | ~ (r2_hidden @ X15 @ (a_2_0_orders_2 @ X12 @ X13)))),
% 0.65/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.65/0.86  thf('67', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B))
% 0.65/0.86          | (r2_orders_2 @ sk_A @ X1 @ 
% 0.65/0.86             (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.65/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86          | ~ (l1_orders_2 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['65', '66'])).
% 0.65/0.86  thf('68', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('69', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('70', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('71', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('72', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B))
% 0.65/0.86          | (r2_orders_2 @ sk_A @ X1 @ 
% 0.65/0.86             (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.65/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (v2_struct_0 @ sk_A))),
% 0.65/0.86      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.65/0.86  thf('73', plain,
% 0.65/0.86      ((![X0 : $i]:
% 0.65/0.86          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86           | (v2_struct_0 @ sk_A)
% 0.65/0.86           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86           | (r2_orders_2 @ sk_A @ X0 @ 
% 0.65/0.86              (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.65/0.86           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.65/0.86           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['62', '72'])).
% 0.65/0.86  thf('74', plain,
% 0.65/0.86      ((![X0 : $i]:
% 0.65/0.86          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.65/0.86           | (r2_orders_2 @ sk_A @ X0 @ 
% 0.65/0.86              (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.65/0.86           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86           | (v2_struct_0 @ sk_A)
% 0.65/0.86           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('simplify', [status(thm)], ['73'])).
% 0.65/0.86  thf('75', plain,
% 0.65/0.86      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86         | (v2_struct_0 @ sk_A)
% 0.65/0.86         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.65/0.86         | (r2_orders_2 @ sk_A @ sk_B @ 
% 0.65/0.86            (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['57', '74'])).
% 0.65/0.86  thf('76', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('77', plain,
% 0.65/0.86      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86         | (v2_struct_0 @ sk_A)
% 0.65/0.86         | (r2_orders_2 @ sk_A @ sk_B @ 
% 0.65/0.86            (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('demod', [status(thm)], ['75', '76'])).
% 0.65/0.86  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('79', plain,
% 0.65/0.86      ((((r2_orders_2 @ sk_A @ sk_B @ 
% 0.65/0.86          (sk_D_1 @ (k1_tarski @ sk_B) @ sk_A @ sk_C))
% 0.65/0.86         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('clc', [status(thm)], ['77', '78'])).
% 0.65/0.86  thf('80', plain,
% 0.65/0.86      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.65/0.86         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup+', [status(thm)], ['53', '79'])).
% 0.65/0.86  thf('81', plain,
% 0.65/0.86      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.65/0.86         <= (((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('simplify', [status(thm)], ['80'])).
% 0.65/0.86  thf('82', plain,
% 0.65/0.86      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.65/0.86         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.65/0.86      inference('split', [status(esa)], ['28'])).
% 0.65/0.86  thf('83', plain,
% 0.65/0.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.65/0.86             ((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['81', '82'])).
% 0.65/0.86  thf('84', plain,
% 0.65/0.86      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.65/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('clc', [status(thm)], ['6', '7'])).
% 0.65/0.86  thf(t5_subset, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i]:
% 0.65/0.86     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.65/0.86          ( v1_xboole_0 @ C ) ) ))).
% 0.65/0.86  thf('85', plain,
% 0.65/0.86      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X7 @ X8)
% 0.65/0.86          | ~ (v1_xboole_0 @ X9)
% 0.65/0.86          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.65/0.86      inference('cnf', [status(esa)], [t5_subset])).
% 0.65/0.86  thf('86', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['84', '85'])).
% 0.65/0.86  thf('87', plain,
% 0.65/0.86      ((![X0 : $i]:
% 0.65/0.86          ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.65/0.86         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.65/0.86             ((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['83', '86'])).
% 0.65/0.86  thf('88', plain,
% 0.65/0.86      (((r2_hidden @ sk_B @ 
% 0.65/0.86         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.65/0.86         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.65/0.86             ((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['35', '87'])).
% 0.65/0.86  thf(t48_orders_2, axiom,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.65/0.86         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.65/0.86       ( ![B:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86           ( ~( r2_hidden @
% 0.65/0.86                B @ 
% 0.65/0.86                ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.65/0.86  thf('89', plain,
% 0.65/0.86      (![X21 : $i, X22 : $i]:
% 0.65/0.86         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.65/0.86          | ~ (r2_hidden @ X21 @ 
% 0.65/0.86               (k1_orders_2 @ X22 @ (k6_domain_1 @ (u1_struct_0 @ X22) @ X21)))
% 0.65/0.86          | ~ (l1_orders_2 @ X22)
% 0.65/0.86          | ~ (v5_orders_2 @ X22)
% 0.65/0.86          | ~ (v4_orders_2 @ X22)
% 0.65/0.86          | ~ (v3_orders_2 @ X22)
% 0.65/0.86          | (v2_struct_0 @ X22))),
% 0.65/0.86      inference('cnf', [status(esa)], [t48_orders_2])).
% 0.65/0.86  thf('90', plain,
% 0.65/0.86      ((((v2_struct_0 @ sk_A)
% 0.65/0.86         | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86         | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86         | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86         | ~ (l1_orders_2 @ sk_A)
% 0.65/0.86         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.65/0.86             ((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['88', '89'])).
% 0.65/0.86  thf('91', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('92', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('93', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('94', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('95', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('96', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A))
% 0.65/0.86         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.65/0.86             ((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('demod', [status(thm)], ['90', '91', '92', '93', '94', '95'])).
% 0.65/0.86  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('98', plain,
% 0.65/0.86      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.65/0.86       ~
% 0.65/0.86       ((r2_hidden @ sk_C @ 
% 0.65/0.86         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['96', '97'])).
% 0.65/0.86  thf('99', plain,
% 0.65/0.86      (~
% 0.65/0.86       ((r2_hidden @ sk_C @ 
% 0.65/0.86         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.65/0.86      inference('sat_resolution*', [status(thm)], ['30', '98'])).
% 0.65/0.86  thf('100', plain,
% 0.65/0.86      (~ (r2_hidden @ sk_C @ 
% 0.65/0.86          (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['29', '99'])).
% 0.65/0.86  thf('101', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | (r2_hidden @ 
% 0.65/0.86           (sk_E @ sk_C @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.65/0.86           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('clc', [status(thm)], ['27', '100'])).
% 0.65/0.86  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('103', plain,
% 0.65/0.86      ((r2_hidden @ 
% 0.65/0.86        (sk_E @ sk_C @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.65/0.86        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.65/0.86      inference('clc', [status(thm)], ['101', '102'])).
% 0.65/0.86  thf('104', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['84', '85'])).
% 0.65/0.86  thf('105', plain,
% 0.65/0.86      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['36', '37'])).
% 0.65/0.86  thf('106', plain,
% 0.65/0.86      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['36', '37'])).
% 0.65/0.86  thf('107', plain,
% 0.65/0.86      ((r2_hidden @ 
% 0.65/0.86        (sk_E @ sk_C @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.65/0.86        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.65/0.86      inference('clc', [status(thm)], ['101', '102'])).
% 0.65/0.86  thf('108', plain,
% 0.65/0.86      (((r2_hidden @ (sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.65/0.86         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['106', '107'])).
% 0.65/0.86  thf('109', plain,
% 0.65/0.86      (((r2_hidden @ (sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.65/0.86         (k1_tarski @ sk_B))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['105', '108'])).
% 0.65/0.86  thf('110', plain,
% 0.65/0.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (r2_hidden @ (sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.65/0.86           (k1_tarski @ sk_B)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['109'])).
% 0.65/0.86  thf('111', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.65/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.86  thf('112', plain,
% 0.65/0.86      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X4 @ X2)
% 0.65/0.86          | ((X4) = (X3))
% 0.65/0.86          | ((X4) = (X0))
% 0.65/0.86          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [d2_tarski])).
% 0.65/0.86  thf('113', plain,
% 0.65/0.86      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.65/0.86         (((X4) = (X0))
% 0.65/0.86          | ((X4) = (X3))
% 0.65/0.86          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['112'])).
% 0.65/0.86  thf('114', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['111', '113'])).
% 0.65/0.86  thf('115', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['114'])).
% 0.65/0.86  thf('116', plain,
% 0.65/0.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | ((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['110', '115'])).
% 0.65/0.86  thf('117', plain,
% 0.65/0.86      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.65/0.86         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['63', '64'])).
% 0.65/0.86  thf('118', plain,
% 0.65/0.86      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.65/0.86         (~ (l1_orders_2 @ X12)
% 0.65/0.86          | ~ (v5_orders_2 @ X12)
% 0.65/0.86          | ~ (v4_orders_2 @ X12)
% 0.65/0.86          | ~ (v3_orders_2 @ X12)
% 0.65/0.86          | (v2_struct_0 @ X12)
% 0.65/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.65/0.86          | (r2_hidden @ X15 @ (a_2_0_orders_2 @ X12 @ X13))
% 0.65/0.86          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.65/0.86          | ((X15) != (X16))
% 0.65/0.86          | ~ (r2_orders_2 @ X12 @ (sk_E @ X16 @ X13 @ X12) @ X16))),
% 0.65/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.65/0.86  thf('119', plain,
% 0.65/0.86      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.65/0.86         (~ (r2_orders_2 @ X12 @ (sk_E @ X16 @ X13 @ X12) @ X16)
% 0.65/0.86          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.65/0.86          | (r2_hidden @ X16 @ (a_2_0_orders_2 @ X12 @ X13))
% 0.65/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.65/0.86          | (v2_struct_0 @ X12)
% 0.65/0.86          | ~ (v3_orders_2 @ X12)
% 0.65/0.86          | ~ (v4_orders_2 @ X12)
% 0.65/0.86          | ~ (v5_orders_2 @ X12)
% 0.65/0.86          | ~ (l1_orders_2 @ X12))),
% 0.65/0.86      inference('simplify', [status(thm)], ['118'])).
% 0.65/0.86  thf('120', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (l1_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.65/0.86               X0))),
% 0.65/0.86      inference('sup-', [status(thm)], ['117', '119'])).
% 0.65/0.86  thf('121', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('122', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('123', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('124', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('125', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.65/0.86               X0))),
% 0.65/0.86      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 0.65/0.86  thf('126', plain,
% 0.65/0.86      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86        | (v2_struct_0 @ sk_A)
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['116', '125'])).
% 0.65/0.86  thf('127', plain,
% 0.65/0.86      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.65/0.86         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.65/0.86      inference('split', [status(esa)], ['39'])).
% 0.65/0.86  thf('128', plain,
% 0.65/0.86      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.65/0.86       ((r2_hidden @ sk_C @ 
% 0.65/0.86         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.65/0.86      inference('split', [status(esa)], ['39'])).
% 0.65/0.86  thf('129', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.86      inference('sat_resolution*', [status(thm)], ['30', '98', '128'])).
% 0.65/0.86  thf('130', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['127', '129'])).
% 0.65/0.86  thf('131', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('132', plain,
% 0.65/0.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86        | (v2_struct_0 @ sk_A)
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('demod', [status(thm)], ['126', '130', '131'])).
% 0.65/0.86  thf('133', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['132'])).
% 0.65/0.86  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('135', plain,
% 0.65/0.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.65/0.86      inference('clc', [status(thm)], ['133', '134'])).
% 0.65/0.86  thf('136', plain,
% 0.65/0.86      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.65/0.86          = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['58', '59'])).
% 0.65/0.86  thf('137', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_C @ 
% 0.65/0.86           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.65/0.86         <= (~
% 0.65/0.86             ((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('split', [status(esa)], ['28'])).
% 0.65/0.86  thf('138', plain,
% 0.65/0.86      (((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (~
% 0.65/0.86             ((r2_hidden @ sk_C @ 
% 0.65/0.86               (k1_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['136', '137'])).
% 0.65/0.86  thf('139', plain,
% 0.65/0.86      (~
% 0.65/0.86       ((r2_hidden @ sk_C @ 
% 0.65/0.86         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.65/0.86      inference('sat_resolution*', [status(thm)], ['30', '98'])).
% 0.65/0.86  thf('140', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['138', '139'])).
% 0.65/0.86  thf('141', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('clc', [status(thm)], ['135', '140'])).
% 0.65/0.86  thf('142', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.65/0.86      inference('demod', [status(thm)], ['104', '141'])).
% 0.65/0.86  thf('143', plain, ($false), inference('sup-', [status(thm)], ['103', '142'])).
% 0.65/0.86  
% 0.65/0.86  % SZS output end Refutation
% 0.65/0.86  
% 0.65/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
